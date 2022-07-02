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
use ark_ec::{bn::{Bn, BnParameters}, short_weierstrass_jacobian::GroupAffine};
use ark_ff::{BigInteger256, FromBytes, PrimeField, ToBytes, BigInteger, Fp256};
use ark_relations::r1cs::{
    ConstraintMatrices, ConstraintSynthesizer, ConstraintSystem, OptimizationGoal,
};
use ark_serialize::{CanonicalDeserialize, SerializationError, Write};
use ark_std::{log2, rand::thread_rng};
use byteorder::{LittleEndian, ReadBytesExt};
use num::{BigInt, BigUint};

use std::{
    collections::HashMap,
    io::{Read, Result as IoResult, Seek, SeekFrom}, path::Path, fs::File, str::FromStr,
};

use ark_bn254::{Bn254, Fq, Fq2, Fr, G1Affine, G2Affine, Parameters, FqParameters};
use ark_groth16::{generate_random_parameters, ProvingKey, VerifyingKey};
use num_traits::Zero;

use crate::CircomCircuit;

fn generate_zkey(circuit: CircomCircuit<Bn<Parameters>>, path: &Path) -> IoResult<()> {
    let mut rng = thread_rng();
    let params = generate_random_parameters::<Bn254, _, _>(circuit.clone(), &mut rng).unwrap();

    let cs = ConstraintSystem::new_ref();
    cs.set_optimization_goal(OptimizationGoal::Constraints);


    let n_pub_inputs = circuit.get_public_inputs().unwrap().len() as u64;
    
    circuit.generate_constraints(cs.clone()).unwrap();
    
    let n_vars = (cs.to_matrices().unwrap().num_witness_variables as u64) + n_pub_inputs + 1;
    let domain_size = n_vars.next_power_of_two();

    let mut file = File::create(path)?;

    //// header
    
    // magic number (zkey)
    let magic = [122u8, 107u8, 101u8, 121u8];
    file.write_all(&magic)?;

    // hardcode to version 1
    let version = 1u32;
    file.write_all(&version.to_le_bytes())?;

    // we'll have 9 sections
    let sections = 9u32;
    file.write_all(&sections.to_le_bytes())?;

    // section 1
    file.write_all(&1u32.to_le_bytes())?;
    file.write_all(&4u64.to_le_bytes())?;
    file.write_all(&1u32.to_le_bytes())?;

    // section 2
    file.write_all(&2u32.to_le_bytes())?;
    file.write_all(&660u64.to_le_bytes())?;

    file.write_all(&32u32.to_le_bytes())?;

    let (_, q) = BigInt::from_str("21888242871839275222246405745257275088696311157297823662689037894645226208583").unwrap().to_bytes_le();
    file.write_all(&q)?;

    file.write_all(&32u32.to_le_bytes())?;
    
    let (_, r) = BigInt::from_str("21888242871839275222246405745257275088548364400416034343698204186575808495617").unwrap().to_bytes_le();
    file.write_all(&r)?;

    file.write_all(&(n_vars as u32).to_le_bytes())?;
    file.write_all(&(n_pub_inputs as u32).to_le_bytes())?;
    file.write_all(&(domain_size as u32).to_le_bytes())?;

    write_g1(params.vk.alpha_g1, &mut file)?;
    write_g1(params.beta_g1, &mut file)?;
    write_g1(params.delta_g1, &mut file)?;

    write_g2(params.vk.beta_g2, &mut file)?;
    write_g2(params.vk.gamma_g2, &mut file)?;
    write_g2(params.vk.delta_g2, &mut file)?;

    // section 3
    file.write_all(&3u32.to_le_bytes())?;
    file.write_all(&((n_pub_inputs + 1) * 64).to_le_bytes())?;

    for el in params.vk.gamma_abc_g1 {
        write_g1(el, &mut file)?;
    }

    // // section 4
    // let matrix_len = 2 * (n_pub_inputs + cs.to_matrices().unwrap().a_num_non_zero as u64);
    // let section_size = 4 + matrix_len * (12 + 32);
    // file.write_all(&4u32.to_le_bytes())?;
    // file.write_all(&section_size.to_le_bytes())?;

    // // TODO: write section

    // // section 5
    // file.write_all(&5u32.to_le_bytes())?;
    // file.write_all(&(n_vars * 32).to_le_bytes())?;

    // // section 6
    // file.write_all(&6u32.to_le_bytes())?;
    // file.write_all(&(n_vars * 32).to_le_bytes())?;

    // // section 7
    // file.write_all(&7u32.to_le_bytes())?;
    // file.write_all(&(n_vars * 32 * 2).to_le_bytes())?;
    
    // // section 8
    // file.write_all(&8u32.to_le_bytes())?;
    // file.write_all(&((cs.to_matrices().unwrap().num_witness_variables as u64) * 32).to_le_bytes())?;

    // // section 9
    // file.write_all(&9u32.to_le_bytes())?;
    // file.write_all(&((cs.to_matrices().unwrap().num_witness_variables as u64) * 32).to_le_bytes())?;

    //dbg!(cs.to_matrices());
    //dbg!(params);

    Ok(())
}

fn write_field(field: Fp256<FqParameters>, file: &mut File) -> IoResult<()> {
    let bigint: BigUint = field.into();
    file.write_all(&bigint.to_bytes_le())
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

    use ark_bn254::{Parameters, Bn254};
    use ark_ec::bn::Bn;
    use ark_groth16::generate_random_parameters;
    use ark_relations::r1cs::{ConstraintSystem, OptimizationGoal, ConstraintSynthesizer};
    use ark_std::rand::thread_rng;

    use crate::{CircomCircuit, CircomConfig, CircomBuilder};

    use super::generate_zkey;

    #[test]
    fn xxx() {
        let cfg = CircomConfig::<Bn254>::new(
            "./test-vectors/mycircuit.wasm",
            "./test-vectors/mycircuit.r1cs",
        )
        .unwrap();
        let mut builder = CircomBuilder::new(cfg);
        builder.push_input("a", 3u32);
        builder.push_input("b", 11u32);

        let circom = builder.build().unwrap();

        generate_zkey(circom, Path::new("test.xxx"));
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
        let mut rng = thread_rng();
        let params = generate_random_parameters::<Bn254, _, _>(circom.clone(), &mut rng).unwrap();

        let cs = ConstraintSystem::new_ref();
        cs.set_optimization_goal(OptimizationGoal::Constraints);

        circom.generate_constraints(cs.clone()).unwrap();
        let xx = cs.to_matrices();

        let duration = start.elapsed();
        println!("zkey generation took: {:?}", duration);




    }
}
