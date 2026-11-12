-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P67.controlled_phase_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T23:13:39.166523+00:00
-- url     : https://prove2.me/submissions/0afd5278-ab86-43f3-9e79-1e34bd4296e4

import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P67

noncomputable section

open scoped ComplexConjugate Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable

open MeasureTheory Filter

variable {I J K L A : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype L] [DecidableEq L] [Fintype A] [DecidableEq A]

open QAlgorithms.Papers.Independent.Intakethird100.P67 in
theorem solution [Nonempty I] (U : Matrix.unitaryGroup I ℂ)
    (z : ℂ) (hz : ‖z‖ = 1) (hne : z ≠ 1) :
    (∀ rho : Matrix I I ℂ, QAlgorithms.IsDensityMatrix rho →
      densityConjugation (z • (U : Matrix I I ℂ)) rho = densityConjugation (U : Matrix I I ℂ) rho) ∧
    ¬ ∃ w : ℂ, ‖w‖ = 1 ∧ systemControlled (z • (U : Matrix I I ℂ)) = w • systemControlled (U : Matrix I I ℂ) := by
  have hzz : z * star z = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hz]
    norm_num
  refine ⟨?_, ?_⟩
  · intro rho _
    unfold densityConjugation
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      hzz, one_smul]
  · rintro ⟨w, _, heq⟩
    obtain ⟨i⟩ := ‹Nonempty I›
    have hsc : ∀ (V : Matrix I I ℂ) (a c : I), systemControlled V (a, true) (c, true) = V a c := by
      intro V a c
      simp [systemControlled, QAlgorithms.controlled]
    have hsc2 : ∀ (V : Matrix I I ℂ) (a : I), systemControlled V (a, false) (a, false) = 1 := by
      intro V a
      simp [systemControlled, QAlgorithms.controlled]
    have h1 := congrFun (congrFun heq (i, false)) (i, false)
    rw [Matrix.smul_apply, hsc2, hsc2, smul_eq_mul, mul_one] at h1
    have hU0 : ∀ a c, (U : Matrix I I ℂ) a c = 0 := by
      intro a c
      have h2 := congrFun (congrFun heq (a, true)) (c, true)
      rw [Matrix.smul_apply, hsc, hsc, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, ← h1] at h2
      have h3 : (z - 1) * (U : Matrix I I ℂ) a c = 0 := by linear_combination h2
      rcases mul_eq_zero.1 h3 with h | h
      · exact absurd (sub_eq_zero.1 h) hne
      · exact h
    have h := congrFun (congrFun (Matrix.mem_unitaryGroup_iff.1 U.2) i) i
    rw [Matrix.mul_apply, Matrix.one_apply_eq] at h
    simp [hU0] at h

end
