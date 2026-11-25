-- Prove2me | solution 1 for PI.HookSteps.highest_weight_last_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:54:59.240086+00:00
-- url     : https://prove2.me/submissions/b9a7db89-ae1a-43f8-8862-a0a5531a6900

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_DetShiftNormOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HookLengthBound_HighestWeightLastZero
import Theorems.Thm_PI_HookSteps_lpMinor_rename
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
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
theorem _root_.solution : HwLastZero := by
  intro n ν _ hl
  simp only [hw]
  rw [Fin.prod_univ_castSucc, map_prod]
  have hlast : nuNext ν (Fin.last n) = 0 := by simp [nuNext]
  rw [hlast, hl, Nat.sub_zero, pow_zero, mul_one]
  refine Finset.prod_congr rfl fun s _ => ?_
  have hs := s.isLt
  rw [map_pow, lpMinor_rename n ((s : ℕ) + 1) _ _ (by omega) (by omega)]
  congr 1
  simp only [nuNext, Fin.val_castSucc]
  rw [dif_pos (show (s : ℕ) + 1 < n + 1 by omega)]
  by_cases h : (s : ℕ) + 1 < n
  · rw [dif_pos h]; rfl
  · rw [dif_neg h]
    have : (⟨s.val + 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp; omega)
    rw [this, hl]
end PI.HookSteps
