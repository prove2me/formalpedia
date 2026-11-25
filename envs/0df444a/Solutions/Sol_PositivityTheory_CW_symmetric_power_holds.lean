-- Prove2me | solution 1 for PositivityTheory.CW.symmetric_power_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:39:38.051125+00:00
-- url     : https://prove2.me/submissions/147dfbc8-1976-4cc3-bbae-4b6e5803be8c

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_SymmetricPowerHolds
import Theorems.Thm_PositivityTheory_CW_identity_filtration_of_scalar_symm_pow

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
namespace PositivityTheory.CW
theorem _root_.solution : A7 := by
  intro W _ _ P hP x hx h0 j
  induction j with
  | zero => simp
  | succ j ih =>
    have hsym := identity_filtration_of_scalar.symm_pow P hP (2 ^ j)

    have key : (inner ℂ x ((P ^ (2 ^ (j + 1))) x)).re = ‖(P ^ (2 ^ j)) x‖ ^ 2 := by
      rw [pow_succ, pow_mul, sq, Module.End.mul_apply, ← hsym]
      exact inner_self_eq_norm_sq (𝕜 := ℂ) ((P ^ (2 ^ j)) x)

    have cs : |(inner ℂ x ((P ^ (2 ^ j)) x)).re| ≤ ‖(P ^ (2 ^ j)) x‖ := by
      calc _ ≤ ‖inner ℂ x ((P ^ (2 ^ j)) x)‖ := Complex.abs_re_le_norm _
        _ ≤ ‖x‖ * ‖(P ^ (2 ^ j)) x‖ := norm_inner_le_norm _ _
        _ = _ := by rw [hx, one_mul]
    have hpos : 0 ≤ (inner ℂ x (P x)).re ^ (2 ^ j) := pow_nonneg h0 _
    calc (inner ℂ x (P x)).re ^ (2 ^ (j + 1)) = ((inner ℂ x (P x)).re ^ (2 ^ j)) ^ 2 := by
          rw [pow_succ, pow_mul]
      _ ≤ ((inner ℂ x ((P ^ (2 ^ j)) x)).re) ^ 2 := pow_le_pow_left₀ hpos ih 2
      _ = |(inner ℂ x ((P ^ (2 ^ j)) x)).re| ^ 2 := (sq_abs _).symm
      _ ≤ ‖(P ^ (2 ^ j)) x‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) cs 2
      _ = _ := key.symm
end PositivityTheory.CW
