-- Prove2me | solution 1 for PI.ZW.zerosWindow_of_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:59:00.877098+00:00
-- url     : https://prove2.me/submissions/21e316d9-4304-4448-b1d4-a748a57519b7

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_FinsumMemLeFinsumMem
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_Jensen
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_RightOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ZeroWindow_Assemble
import Theorems.Thm_PI_ZW_rightChi
import Theorems.Thm_PI_ZW_rightOne
import Theorems.Thm_PI_ZW_rightHalf_of
import Theorems.Thm_PI_ZW_zerosWindowWith_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.ZW
namespace PI.ZW
theorem _root_.solution (hT : Transfer) :
    PI.LBoundRight → PI.ZetaBoundRight → PI.LInvRight → PI.ZerosWindow := by
  intro hL hZ hI
  obtain ⟨C₁, h₁⟩ := rightChi hL hI
  obtain ⟨C₂, h₂⟩ := rightOne hZ hI
  have hlog : ∀ (N : ℕ) [NeZero N] (t : ℝ), 0 ≤ Real.log (↑N * (|t| + 2)) := by
    intro N _ t
    apply Real.log_nonneg
    have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
    nlinarith [abs_nonneg t, mul_nonneg (sub_nonneg.mpr hN) (add_nonneg (abs_nonneg t) zero_le_two)]
  have h₁' : RightChiWith (max C₁ 1) := by
    unfold RightChiWith at h₁ ⊢
    intro N _ χ hχ t
    obtain ⟨hf, hs⟩ := h₁ N χ hχ t
    exact ⟨hf, hs.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hlog N t))⟩
  have h₂' : RightOneWith (max C₂ 1) := by
    unfold RightOneWith at h₂ ⊢
    intro N _ χ hχ t
    obtain ⟨hf, hs⟩ := h₂ N χ hχ t
    exact ⟨hf, hs.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hlog N t))⟩
  have hw := zerosWindowWith_of _ (rightHalf_of _ _ h₁' h₂') hT
  unfold PI.ZerosWindow
  exact ⟨_, mul_pos two_pos (lt_of_lt_of_le one_pos (le_trans (le_max_right C₁ 1) (le_max_left _ _))), hw⟩
end PI.ZW
