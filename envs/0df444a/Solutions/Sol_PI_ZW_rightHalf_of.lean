-- Prove2me | solution 1 for PI.ZW.rightHalf_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:28:46.823825+00:00
-- url     : https://prove2.me/submissions/33cdd563-89eb-459d-aba7-54c95f27defc

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightHalfWith
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_FinsumMemLeFinsumMem
import Theorems.Thm_PI_ZW_log_mul_abs_add_two_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.ZW
open DirichletCharacter
namespace PI.ZW
theorem _root_.solution (C₁ C₂ : ℝ) (h₁ : RightChiWith C₁) (h₂ : RightOneWith C₂) :
    RightHalfWith (max C₁ C₂) := by
  intro N _ χ hχ t
  have hl := log_mul_abs_add_two_nonneg N t
  rcases hχ with h | h
  · obtain ⟨hf, hs⟩ := h₁ N χ h t
    exact ⟨hf, hs.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hl)⟩
  · obtain ⟨hf, hs⟩ := h₂ N χ h t
    exact ⟨hf, hs.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hl)⟩
end PI.ZW
