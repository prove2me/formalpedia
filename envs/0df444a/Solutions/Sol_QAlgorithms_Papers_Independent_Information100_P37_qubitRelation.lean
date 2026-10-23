-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P37.qubitRelation
-- status  : ACCEPTED   (disprove)
-- author  : @fizzyinc3
-- created : 2026-10-22T12:55:01.33944+00:00
-- url     : https://prove2.me/submissions/cb7da8cf-c66a-4fb6-b599-4857b29f69ff

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

lemma X7H_aniso (i j : Fin 2) : anisotropy (response X7H_U) i j = if i = j then 0 else -1 := by
  have htr : (response X7H_U).trace = 1 := by
    simp [Matrix.trace, Fin.sum_univ_two, X7H_resp]; norm_num
  simp only [anisotropy, Matrix.sub_apply, Matrix.smul_apply, htr, X7H_resp, X7H_zsp,
    Fintype.card_fin, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp <;> norm_num

lemma X7H_excess_sq : excess (response X7H_U) ^ 2 = 1 / 30 := by
  rw [excess, Real.sq_sqrt (by
    apply div_nonneg
    · unfold realFrobeniusSq diagonalSq; positivity
    · unfold fourthDenominator; positivity)]
  simp [realFrobeniusSq, diagonalSq, Fin.sum_univ_two, X7H_aniso, fourthDenominator]
  norm_num

end QAlgorithms.Papers.Independent.Information100.P37

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P37 in
theorem solution : ¬ (∀ (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin 2) ℂ),
    cgpd (conjSuperop U) = (2 / Real.sqrt 5) * cgp (conjSuperop U) ∧
    excess (response U) = 0 ∧
    (∀ t : ℝ, cgp (conjSuperop (((rotY (2 * t)).submatrix (fun i : Fin 2 => i.val == 1) (fun j : Fin 2 => j.val == 1)))) = Real.sin (2 * t) ^ 2 / 6 ∧
      cgpd (conjSuperop (((rotY (2 * t)).submatrix (fun i : Fin 2 => i.val == 1) (fun j : Fin 2 => j.val == 1)))) = Real.sin (2 * t) ^ 2 / (3 * Real.sqrt 5))) := by
  intro h
  have h1 := (h X7H_U X7H_unitary).2.1
  have h2 := X7H_excess_sq
  rw [h1] at h2
  norm_num at h2
