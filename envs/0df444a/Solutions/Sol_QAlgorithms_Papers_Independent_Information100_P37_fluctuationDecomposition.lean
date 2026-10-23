-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P37.fluctuationDecomposition
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-22T12:45:56.272538+00:00
-- url     : https://prove2.me/submissions/28593e6d-584c-444b-a6ca-3b098dfcc3c8

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P37

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Matrix ComplexConjugate Topology

namespace QAlgorithms.Papers.Independent.Information100.P37

def X7H_U : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 + Complex.I) / 2, (1 - Complex.I) / 2; (1 - Complex.I) / 2, (1 + Complex.I) / 2]

lemma X7H_unitary : X7H_U ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [X7H_U, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply, map_ofNat] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring_nf

lemma X7H_trans (i j : Fin 2) : transition X7H_U i j = 1 / 2 := by
  fin_cases i <;> fin_cases j <;> simp [transition, X7H_U, Complex.normSq_apply] <;> norm_num

lemma X7H_resp (i j : Fin 2) : response X7H_U i j = (if i = j then 1 else 0) - 1 / 2 := by
  simp only [response, Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply, Matrix.transpose_apply,
    X7H_trans, Fin.sum_univ_two]
  norm_num

lemma X7H_zsp {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    zeroSumProjector ι i j = 1 - 1 / (Fintype.card ι : ℝ) := rfl

universe u

lemma X7L_sum {M : Type*} [AddCommMonoid M] (f : ULift.{u} (Fin 2) → M) :
    ∑ x, f x = f ⟨0⟩ + f ⟨1⟩ := by
  rw [← Equiv.ulift.{u}.symm.sum_comp]
  simp [Fin.sum_univ_two, Equiv.ulift]

lemma X7L_card : Fintype.card (ULift.{u} (Fin 2)) = 2 := by simp

def X7L_U : Matrix (ULift.{u} (Fin 2)) (ULift.{u} (Fin 2)) ℂ :=
  X7H_U.submatrix Equiv.ulift Equiv.ulift

lemma X7L_unitary : X7L_U.{u} ∈ Matrix.unitaryGroup (ULift.{u} (Fin 2)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, X7L_U, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, ← Matrix.star_eq_conjTranspose,
    Matrix.mem_unitaryGroup_iff.mp X7H_unitary, Matrix.submatrix_one_equiv]

lemma X7L_trans (i j : ULift.{u} (Fin 2)) : transition X7L_U.{u} i j = 1 / 2 :=
  X7H_trans _ _

lemma X7L_resp (i j : ULift.{u} (Fin 2)) :
    response X7L_U.{u} i j = (if i = j then 1 else 0) - 1 / 2 := by
  simp only [response, Matrix.sub_apply, Matrix.one_apply, Matrix.mul_apply,
    Matrix.transpose_apply, X7L_trans, X7L_sum]
  norm_num

end QAlgorithms.Papers.Independent.Information100.P37

universe u

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P37 in
/-- Disproof: with `zeroSumProjector` the constant `1 - 1/d` matrix, the anisotropy of the
response of a flat qubit unitary does not annihilate the all-ones vector. -/
theorem solution : ¬ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (hd : 2 ≤ Fintype.card ι)
    (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ),
    let G := response U
    cgpd (conjSuperop U) ^ 2 = gammaFactor (Fintype.card ι) ^ 2 * cgp (conjSuperop U) ^ 2 + excess G ^ 2 ∧
    excess G ^ 2 = (2 * realFrobeniusSq (anisotropy G) + 6 * diagonalSq (anisotropy G)) /
      fourthDenominator (Fintype.card ι) ∧
    0 ≤ excess G ^ 2 ∧ (anisotropy G).mulVec (fun _ => 1) = 0 ∧ (anisotropy G).trace = 0 ∧
    (excess G = 0 ↔ anisotropy G = 0) ∧
    (anisotropy G = 0 ↔ G = (G.trace / ((Fintype.card ι : ℝ) - 1)) • zeroSumProjector ι)) := by
  intro h
  have h4 := (@h (ULift.{0} (Fin 2)) _ _ (by rw [X7L_card]) X7L_U X7L_unitary).2.2.2.1
  have h0 := congrFun h4 ⟨0⟩
  simp only [anisotropy, Matrix.mulVec, dotProduct, X7L_sum, Matrix.sub_apply,
    Matrix.smul_apply, X7L_resp, X7H_zsp, Matrix.trace, Matrix.diag, smul_eq_mul, mul_one,
    Pi.zero_apply, X7L_card] at h0
  norm_num at h0
