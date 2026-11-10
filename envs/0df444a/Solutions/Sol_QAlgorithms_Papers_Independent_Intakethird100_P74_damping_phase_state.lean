-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P74.damping_phase_state
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T02:57:59.911089+00:00
-- url     : https://prove2.me/submissions/1fd66b8a-40e9-4659-982b-654afc40558b

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P74

open QAlgorithms

open scoped ComplexConjugate Matrix

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

open QAlgorithms.Papers.Independent.Intakethird100.P74 in
theorem solution (eta : ℝ) (he0 : 0 ≤ eta) (he1 : eta ≤ 1) (x : Bool) :
    dampingPhaseOutput eta x = Matrix.of (fun p q =>
      dampingPhaseMatrix eta x (cbIndex p) (cbIndex q)) := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]; norm_num
  have hη : ((Real.sqrt eta : ℝ) : ℂ) * ((Real.sqrt eta : ℝ) : ℂ) = (eta : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt he0]
  have hη' : ((Real.sqrt (1 - eta) : ℝ) : ℂ) * ((Real.sqrt (1 - eta) : ℝ) : ℂ) = 1 - (eta : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]; push_cast; ring
  have hsub : (1 : ℝ) - (1 - eta) = eta := by ring
  have h2ne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; positivity
  ext ⟨a, i⟩ ⟨b, j⟩
  cases a <;> cases i <;> cases b <;> cases j <;> cases x <;>
    simp [dampingPhaseOutput, idTensorSuperop, dampingMap,
      QAlgorithms.Papers.Independent.Independent2.P01.damping, krausApply,
      QAlgorithms.Papers.Independent.Independent2.P01.dampingKraus, pureDensity,
      binaryPhaseBellVector, bitSign, cbIndex, dampingPhaseMatrix, Matrix.mul_apply,
      Fintype.sum_bool, Matrix.conjTranspose_apply, Matrix.diagonal_apply, hsub] <;>
    field_simp <;>
    first
      | ring1
      | linear_combination (-1 : ℂ) * h2
      | linear_combination (-((Real.sqrt eta : ℝ) : ℂ)) * h2
      | linear_combination ((Real.sqrt eta : ℝ) : ℂ) * h2
      | linear_combination (-(1 - (eta : ℂ))) * h2 + 2 * hη'
      | linear_combination (-(eta : ℂ)) * h2 + 2 * hη
