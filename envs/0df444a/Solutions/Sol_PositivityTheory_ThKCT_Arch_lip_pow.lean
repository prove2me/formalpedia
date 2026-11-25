-- Prove2me | solution 1 for PositivityTheory.ThKCT.Arch.lip_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:46:13.760588+00:00
-- url     : https://prove2.me/submissions/e48c0a0a-c85c-4148-b3e3-a4ce32234793

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_SliceArch
import Theorems.Thm_PositivityTheory_ThKCT_Arch_Bd_succ
import Theorems.Thm_PositivityTheory_ThKCT_Arch_lip

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PositivityTheory PositivityTheory.ThKCT PositivityTheory.ThKCT.Arch
open scoped ContDiff NNReal
open Complex Filter Topology
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
namespace PositivityTheory.ThKCT.Arch
theorem _root_.solution (n : ℕ) : ∀ q : Seminorm ℂ (SchwartzMap V ℂ), Continuous q → ∃ p : Seminorm ℂ (SchwartzMap V ℂ),
    Continuous p ∧ ∀ w f, ‖w‖ ≤ 1 → q ((fun g => S w g - g)^[n] f) ≤ ‖w‖ ^ n * p f := by
  induction n with
  | zero => exact fun q hq => ⟨q, hq, fun w f _ => by simp⟩
  | succ n ih =>
    intro q hq
    obtain ⟨p, hp, h⟩ := ih q hq
    obtain ⟨p', hp', h'⟩ := lip p hp
    refine ⟨p', hp', fun w f hw => ?_⟩
    rw [Function.iterate_succ_apply, pow_succ, mul_assoc]
    exact (h w _ hw).trans (mul_le_mul_of_nonneg_left (h' w f hw) (by positivity))
end PositivityTheory.ThKCT.Arch
