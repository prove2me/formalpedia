-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P37.complexHadamard
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-22T12:45:55.400989+00:00
-- url     : https://prove2.me/submissions/435c1161-2a13-44a0-9987-ee59dbce1356

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
/-- Disproof: `zeroSumProjector` is the constant matrix with entries `1 - 1/d` (its `1` is the
all-ones function), while a flat unitary has response `I - J/d`. -/
theorem solution : ¬ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (hd : 2 ≤ Fintype.card ι)
    (U : Matrix ι ι ℂ) (hU : U ∈ Matrix.unitaryGroup ι ℂ) (hf : IsFlat U),
    let d := (Fintype.card ι : ℝ)
    cgp (conjSuperop U) = (d - 1) / (d * (d + 1)) ∧
    cgpd (conjSuperop U) = 2 * Real.sqrt (d - 1) / ((d + 1) * Real.sqrt ((d + 2) * (d + 3))) ∧
    selectivity (conjSuperop U) = 1 ∧ response U = zeroSumProjector ι) := by
  intro h
  have hflat : IsFlat X7L_U.{0} := by
    intro i j; rw [X7L_trans, X7L_card]; norm_num
  have h4 := (@h (ULift.{0} (Fin 2)) _ _ (by rw [X7L_card]) X7L_U X7L_unitary hflat).2.2.2
  have h01 := congrFun (congrFun h4 ⟨0⟩) ⟨1⟩
  rw [X7L_resp, X7H_zsp, X7L_card] at h01
  norm_num at h01
