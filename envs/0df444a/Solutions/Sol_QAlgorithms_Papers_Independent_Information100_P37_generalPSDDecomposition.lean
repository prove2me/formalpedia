-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P37.generalPSDDecomposition
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-22T12:45:57.173842+00:00
-- url     : https://prove2.me/submissions/fd53117d-138f-4eb0-b0c2-4036147059dd

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
/-- Disproof: with `zeroSumProjector` the constant `1 - 1/d` matrix, the anisotropy of
`G = [[1,-1],[-1,1]]` (PSD, zero row sums) does not annihilate the all-ones vector. -/
theorem solution : ¬ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (hd : 2 ≤ Fintype.card ι)
    (G : Matrix ι ι ℝ) (hp : G.PosSemidef) (hz : G.mulVec (fun _ => 1) = 0),
    let d := (Fintype.card ι : ℝ)
    let A := anisotropy G
    let v := ∫ p, (quadratic G p - ∫ q, quadratic G q ∂simplexLaw ι) ^ 2 ∂simplexLaw ι
    A.mulVec (fun _ => 1) = 0 ∧ A.trace = 0 ∧
    (G * G).trace = G.trace ^ 2 / (d - 1) + realFrobeniusSq A ∧
    diagonalSq G = G.trace ^ 2 / d + diagonalSq A ∧
    v = 4 * G.trace ^ 2 / ((d - 1) * (d + 1) ^ 2 * (d + 2) * (d + 3)) +
      (2 * realFrobeniusSq A + 6 * diagonalSq A) / fourthDenominator (Fintype.card ι) ∧
    (v = 4 * G.trace ^ 2 / ((d - 1) * (d + 1) ^ 2 * (d + 2) * (d + 3)) ↔ A = 0)) := by
  intro h
  let w : Matrix (Fin 1) (Fin 2) ℝ := !![1, -1]
  have hG : (wᴴ * w) = !![1, -1; -1, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [w, Matrix.mul_apply]
  have hp0 : (!![1, -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℝ).PosSemidef := by
    rw [← hG]; exact Matrix.posSemidef_conjTranspose_mul_self w
  let G : Matrix (ULift.{0} (Fin 2)) (ULift.{0} (Fin 2)) ℝ :=
    (!![1, -1; -1, 1] : Matrix (Fin 2) (Fin 2) ℝ).submatrix Equiv.ulift Equiv.ulift
  have hp : G.PosSemidef := hp0.submatrix _
  have hz : G.mulVec (fun _ => 1) = 0 := by
    ext ⟨i⟩; fin_cases i <;> simp [G, Matrix.mulVec, dotProduct, X7L_sum, Equiv.ulift]
  have h1 := (@h (ULift.{0} (Fin 2)) _ _ (by rw [X7L_card]) G hp hz).1
  have h0 := congrFun h1 ⟨0⟩
  simp only [anisotropy, Matrix.mulVec, dotProduct, X7L_sum, Matrix.sub_apply,
    Matrix.smul_apply, X7H_zsp, Matrix.trace, Matrix.diag, smul_eq_mul, mul_one,
    Pi.zero_apply, X7L_card, G, Matrix.submatrix_apply] at h0
  norm_num [Equiv.ulift] at h0
