//! ZKey Parsing
//!
//! Each ZKey file is broken into sections:
//!  Header(1)
//!       Prover Type 1 Groth
//!  HeaderGroth(2)
//!       n8q
//!       q
//!       n8r
//!       r
//!       NVars
//!       NPub
//!       DomainSize  (multiple of 2
//!       alpha1
//!       beta1
//!       delta1
//!       beta2
//!       gamma2
//!       delta2
//!  IC(3)
//!  Coefs(4)
//!  PointsA(5)
//!  PointsB1(6)
//!  PointsB2(7)
//!  PointsC(8)
//!  PointsH(9)
//!  Contributions(10)
use ark_ec::{
    bn::{Bn, BnParameters},
    short_weierstrass_jacobian::GroupAffine,
};
use ark_ff::{BigInteger, BigInteger256, Fp256, FpParameters, FromBytes, PrimeField, ToBytes, One};
use ark_relations::r1cs::{
    ConstraintMatrices, ConstraintSynthesizer, ConstraintSystem, ConstraintSystemRef,
    OptimizationGoal,
};
use ark_serialize::{CanonicalDeserialize, SerializationError, Write};
use ark_std::{log2, rand::thread_rng};
use byteorder::{LittleEndian, ReadBytesExt};
use num::{BigInt, BigUint};

use std::{
    collections::HashMap,
    fs::File,
    io::{Read, Result as IoResult, Seek, SeekFrom},
    path::Path,
    str::FromStr,
};

use ark_bn254::{Bn254, Fq, Fq2, FqParameters, Fr, FrParameters, G1Affine, G2Affine, Parameters};
use ark_groth16::{generate_random_parameters, ProvingKey, VerifyingKey};
use num_traits::Zero;

use crate::CircomCircuit;

fn generate_parameters(
    circuit: CircomCircuit<Bn<Parameters>>,
) -> (
    ProvingKey<Bn<Parameters>>,
    ConstraintMatrices<Fp256<FrParameters>>,
) {
    let mut rng = thread_rng();
    let params = generate_random_parameters::<Bn254, _, _>(circuit.clone(), &mut rng).unwrap();

    let cs = ConstraintSystem::new_ref();
    cs.set_optimization_goal(OptimizationGoal::Constraints);

    circuit.generate_constraints(cs.clone()).unwrap();

    (params, cs.to_matrices().unwrap())
}

fn serialize_zkey(
    params: ProvingKey<Bn<Parameters>>,
    matrices: ConstraintMatrices<Fp256<FrParameters>>,
    path: &Path,
) -> IoResult<()> {
    let n_pub_inputs = (matrices.num_instance_variables as u64) - 1;
    let n_vars = (matrices.num_witness_variables as u64) + n_pub_inputs;
    let domain_size = n_vars.next_power_of_two();

    dbg!(n_vars);

    let mut file = File::create(path)?;

    //// header

    // magic number (zkey)
    let magic = [122u8, 107u8, 101u8, 121u8];
    file.write_all(&magic)?;

    // hardcode to version 1
    let version = 1u32;
    file.write_all(&version.to_le_bytes())?;

    let sections = 10u32;
    file.write_all(&sections.to_le_bytes())?;

    // section 1
    file.write_all(&1u32.to_le_bytes())?;
    file.write_all(&4u64.to_le_bytes())?;
    file.write_all(&1u32.to_le_bytes())?;

    // section 2
    write_section_header(2, 660, &mut file)?;

    file.write_all(&32u32.to_le_bytes())?;
    file.write_all(&FqParameters::MODULUS.to_bytes_le())?;
    file.write_all(&32u32.to_le_bytes())?;
    file.write_all(&FrParameters::MODULUS.to_bytes_le())?;

    file.write_all(&(n_vars as u32).to_le_bytes())?;
    file.write_all(&(n_pub_inputs as u32).to_le_bytes())?;
    file.write_all(&(domain_size as u32).to_le_bytes())?;

    write_g1(params.vk.alpha_g1, &mut file)?;
    write_g1(params.beta_g1, &mut file)?;
    write_g2(params.vk.beta_g2, &mut file)?;
    write_g2(params.vk.gamma_g2, &mut file)?;
    write_g1(params.delta_g1, &mut file)?;
    write_g2(params.vk.delta_g2, &mut file)?;

    // section 3
    write_section_header(3, (n_pub_inputs + 1) * 64, &mut file)?;

    for el in params.vk.gamma_abc_g1 {
        write_g1(el, &mut file)?;
    }

    // section 4
    let matrix_len = 2 * (n_pub_inputs + matrices.a_num_non_zero as u64);
    let section_size = 4 + matrix_len * (12 + 32);
    dbg!(section_size);
    write_section_header(4, section_size, &mut file)?;

    file.write_all(&(matrix_len as u32).to_le_bytes())?;

    for (m_idx, matrix) in vec![matrices.a, matrices.b].into_iter().enumerate() {
        for (c_idx, entry) in matrix.into_iter().enumerate() {
            for (value, signal) in entry {
                file.write_all(&(m_idx as u32).to_le_bytes())?;
                file.write_all(&(c_idx as u32).to_le_bytes())?;
                file.write_all(&(signal as u32).to_le_bytes())?;
                write_field_fr(value, &mut file)?;
            }
        }
    }

    for i in 0..(n_pub_inputs + 1) as u32 {
        file.write_all(&0u32.to_le_bytes())?;
        file.write_all(&(i + matrices.num_constraints as u32).to_le_bytes())?;
        file.write_all(&i.to_le_bytes())?;
        write_field_fr(Fr::one(), &mut file)?;
    }

    // section 5
    write_section_header(5, n_vars * 64, &mut file)?;

    for el in params.a_query {
        write_g1(el, &mut file)?;
    }

    // section 6
    write_section_header(6, n_vars * 64, &mut file)?;

    for el in params.b_g1_query {
        write_g1(el, &mut file)?;
    }

    // section 7
    write_section_header(7, n_vars * 128, &mut file)?;

    for el in params.b_g2_query {
        write_g2(el, &mut file)?;
    }

    // section 8
    write_section_header(8, ((matrices.num_witness_variables - 1) as u64) * 64, &mut file)?;

    for el in params.l_query {
        write_g1(el, &mut file)?;
    }

    // section 9
    write_section_header(9, (domain_size as u64) * 64, &mut file)?;

    for el in params.h_query {
        write_g1(el, &mut file)?;
    }

    // section 10 
    write_section_header(10, 68, &mut file)?;
    // TODO: fix circuit hash
    file.write_all(&[0u8; 68])?;

    Ok(())
}

fn write_section_header(section_id: u32, section_size: u64, file: &mut File) -> IoResult<()> {
    file.write_all(&section_id.to_le_bytes())?;
    file.write_all(&section_size.to_le_bytes())?;
    Ok(())
}

fn write_field(field: Fp256<FqParameters>, file: &mut File) -> IoResult<()> {
    file.write_all(&field.0.to_bytes_le())
}

fn write_field_fr(field: Fp256<FrParameters>, file: &mut File) -> IoResult<()> {
    file.write_all(&Fr::from_repr(field.0).unwrap().0.to_bytes_le())
}

fn write_g1(point: G1Affine, file: &mut File) -> IoResult<()> {
    write_field(point.x, file)?;
    write_field(point.y, file)?;
    Ok(())
}

fn write_g2(point: G2Affine, file: &mut File) -> IoResult<()> {
    write_field(point.x.c0, file)?;
    write_field(point.x.c1, file)?;
    write_field(point.y.c0, file)?;
    write_field(point.y.c1, file)?;
    Ok(())
}

mod tests {
    use std::{fs::File, path::Path, time::Instant};

    use ark_bn254::{Bn254, Parameters};
    use ark_ec::bn::Bn;
    use ark_groth16::generate_random_parameters;
    use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystem, OptimizationGoal};
    use ark_std::rand::thread_rng;

    use crate::{read_zkey, CircomBuilder, CircomCircuit, CircomConfig, zkey_writer::generate_parameters};

    use super::serialize_zkey;

    #[test]
    fn xxx() {
        let path = "./test-vectors/test.zkey";
        let mut file = File::open(path).unwrap();
        let (params, matrices) = read_zkey(&mut file).unwrap();

        serialize_zkey(params, matrices, Path::new("test.xxx")).unwrap();
    }

    #[test]
    fn yyy() {
        let cfg = CircomConfig::<Bn254>::new(
            "./test-vectors/pubkeygen.wasm",
            "./test-vectors/pubkeygen.r1cs",
        )
        .unwrap();
        let mut builder = CircomBuilder::new(cfg);
        builder.push_input("privkey", 0);
        builder.push_input("privkey", 7);
        builder.push_input("privkey", 6);
        builder.push_input("privkey", 2);

        let start = Instant::now();
        let circom = builder.build().unwrap();
        let duration = start.elapsed();
        println!("witness generation took: {:?}", duration);

        let start = Instant::now();
        
        let (params, matrices) = generate_parameters(circom);
        serialize_zkey(params, matrices, Path::new("pubkeygen.zkey")).unwrap();

        let duration = start.elapsed();
        println!("zkey generation took: {:?}", duration);
    }
}
