-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P09.cnotDecomposition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:40:55.139287+00:00
-- url     : https://prove2.me/submissions/a7336604-4f60-4327-a273-1043d21b0406

import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P09_Model
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 4096
noncomputable section
open scoped Matrix ComplexOrder NNReal ENNReal
open QAlgorithms QAlgorithms.ErrorMitigation QAlgorithms.Papers.Independent.Independent1.P09

private def rawA : Fin 12 → Matrix Bool Bool ℂ :=
  ![1,pauliZ,1,1+Complex.I • pauliZ,pauliZ,1+Complex.I • pauliZ,
    pauliZ,1+Complex.I • pauliZ,1,(2⁻¹:ℂ) • (1+pauliZ),
    pauliZ,(2⁻¹:ℂ) • (1+pauliZ)]
private def rawB : Fin 12 → Matrix Bool Bool ℂ :=
  ![pauliX,1,1+Complex.I • pauliX,1,1+Complex.I • pauliX,pauliX,
    pauliX,1+Complex.I • pauliX,(2⁻¹:ℂ) • (1+pauliX),1,
    (2⁻¹:ℂ) • (1+pauliX),pauliX]
private def gateScale : Fin 12 → ℂ :=
  let s : ℂ := (Real.sqrt 2 : ℂ)⁻¹
  ![1,1,s,s,s,s,1,1/2,1,1,1,1]
private def mapScale : Fin 12 → ℂ :=
  ![1,1,1/2,1/2,1/2,1/2,1,1/4,1,1,1,1]

private lemma sqrt_inv_sq :
    ((Real.sqrt 2 : ℂ)⁻¹) * ((Real.sqrt 2 : ℂ)⁻¹) = (2:ℂ)⁻¹ := by
  norm_cast
  rw [← mul_inv, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

private lemma gate_factor (j : Fin 12) :
    Matrix.kronecker (tableIMatrix (cnotTerms j).1.1)
      (tableIMatrix (cnotTerms j).1.2) =
    gateScale j • Matrix.kronecker (rawA j) (rawB j) := by
  fin_cases j <;>
    dsimp [cnotTerms, tableIMatrix, gateScale, rawA, rawB] <;>
    simp only [Matrix.smul_kronecker, Matrix.kronecker_smul, smul_smul, sqrt_inv_sq,
      one_smul, one_mul, one_div]

private lemma scale_sq (j : Fin 12) : star (gateScale j) * gateScale j = mapScale j := by
  fin_cases j <;>
    norm_num [gateScale, mapScale, Complex.star_def, sqrt_inv_sq]

private lemma operation_factor (j : Fin 12)
    (X : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    conjSuperop (Matrix.kronecker (tableIMatrix (cnotTerms j).1.1)
      (tableIMatrix (cnotTerms j).1.2)) X =
    mapScale j • conjSuperop (Matrix.kronecker (rawA j) (rawB j)) X := by
  simp only [gate_factor, conjSuperop, Matrix.conjTranspose_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, scale_sq]

private lemma rational_identity (X : Matrix (Bool × Bool) (Bool × Bool) ℂ) :
    conjSuperop cnot X = ∑ j : Fin 12, (((cnotTerms j).2 : ℂ)*mapScale j) •
      conjSuperop (Matrix.kronecker (rawA j) (rawB j)) X := by
  ext ⟨a,b⟩ ⟨c,d⟩
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [conjSuperop, cnot, cnotTerms, mapScale, rawA, rawB,
      Fin.sum_univ_succ, Matrix.mul_apply, Fintype.sum_prod_type, Fintype.sum_bool,
      Matrix.kronecker_apply, Matrix.conjTranspose_apply, Matrix.diagonal_apply,
      Matrix.one_apply, pauliX, pauliZ, Matrix.sum_apply, Complex.star_def,
      Complex.conj_ofNat, Complex.conj_inv] <;>
    ring_nf <;> norm_num [pow_succ, Complex.I_mul_I] <;> ring

theorem solution :
    (∀ X : Matrix (Bool × Bool) (Bool × Bool) ℂ,
      conjSuperop cnot X = ∑ j : Fin 12, ((cnotTerms j).2 : ℂ) •
        conjSuperop (Matrix.kronecker (tableIMatrix (cnotTerms j).1.1)
          (tableIMatrix (cnotTerms j).1.2)) X) ∧
    (∑ j : Fin 12, |(cnotTerms j).2|) = 9 := by
  constructor
  · intro X
    simp only [operation_factor, smul_smul]
    exact rational_identity X
  · norm_num [cnotTerms, Fin.sum_univ_succ]

#print axioms solution
