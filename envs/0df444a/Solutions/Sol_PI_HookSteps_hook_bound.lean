-- Prove2me | solution 1 for PI.HookSteps.hook_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:10:48.557815+00:00
-- url     : https://prove2.me/submissions/342eaf13-23e0-4a95-931a-d5ceb3e1a150

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShiftNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DiagonalMonomialFactorial
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_ProdFactorialLe
import Theorems.Thm_PI_HookSteps_prod_factorial_le
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
import Theorems.Thm_PI_HookLower_one_le_cNu
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open MvPolynomial Formalism.GradedWeylDivisibility
noncomputable section
open PI PI.HookSteps
namespace PI.HookSteps
theorem _root_.solution : HookBoundOf := by
  unfold HookBoundOf PI.HookBound
  intro hH N hN ν hν
  have h1 := PI.HookLower.one_le_cNu ν hν
  refine ⟨h1, ?_⟩
  have hD : (0 : ℝ) < ∏ l, ((ν l).factorial : ℝ) :=
    Finset.prod_pos fun l _ => by exact_mod_cast (ν l).factorial_pos
  unfold PI.cNu at h1 ⊢
  have hF0r : (0 : ℝ) ≤ (fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) : ℝ) := by
    have := (one_le_div hD).1 h1
    linarith
  have hF0 : (0 : ℚ) ≤ fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) := by exact_mod_cast hF0r
  have hP : (1 : ℚ) ≤ ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, ((ν i - ν j + (j - i) : ℕ) : ℚ) := by
    calc (1 : ℚ) = ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (1 : ℚ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => by positivity) fun i _ =>
          Finset.prod_le_prod (fun _ _ => zero_le_one) fun j hj => by
            have hij' : i < j := Finset.mem_Ioi.1 hj
            have hij : (i : ℕ) < j := hij'
            exact_mod_cast (show 1 ≤ ν i - ν j + (j - i) by omega)
  have hQ := hH N ν hν
  have hFQ : fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) ≤
      ∏ i : Fin N, (((ν i + (N - 1 - i)).factorial : ℕ) : ℚ) := by
    rw [← hQ]
    exact le_mul_of_one_le_right hF0 hP
  have hFQr : (fockQ (hw ℚ le_rfl ν) (hw ℚ le_rfl ν) : ℝ) ≤
      ∏ i : Fin N, (((ν i + (N - 1 - i)).factorial : ℕ) : ℝ) := by exact_mod_cast hFQ
  have hle : (∏ i : Fin N, (((ν i + (N - 1 - i)).factorial : ℕ) : ℝ)) ≤
      (∏ i, ((ν i).factorial : ℝ)) * ((ν ⟨0, hN⟩ : ℝ) + N) ^ (N * (N - 1) / 2) := by
    exact_mod_cast prod_factorial_le N hN ν hν
  rw [div_le_iff₀ hD]
  linarith
end PI.HookSteps
