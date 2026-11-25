-- Prove2me | solution 1 for PositivityTheory.ThKCT.Arch.ph_sub_bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:16:10.246082+00:00
-- url     : https://prove2.me/submissions/97869acb-6f5e-4a38-bf10-7f6261b0a80b

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_SliceArch
import Theorems.Thm_PositivityTheory_ThKCT_Arch_ph_smooth
import Theorems.Thm_PositivityTheory_ThKCT_Arch_ph_bd

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
theorem _root_.solution (l : V →L[ℝ] ℝ) (c : ℝ) {δ : ℝ} (h1 : δ ≤ 1) (hl : ‖l‖ ≤ δ) (hc : |c| ≤ δ) (i : ℕ) (x : V) :
    ‖iteratedFDeriv ℝ i (fun x => ph l c x - 1) x‖ ≤ δ * (1 + ‖x‖) ^ 1 := by
  have h0 : 0 ≤ δ := (norm_nonneg _).trans hl
  rcases i with _ | i
  · rw [norm_iteratedFDeriv_zero, ph]
    refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ((norm_add_le _ _).trans ?_)
    have := l.le_opNorm x
    rw [Real.norm_eq_abs c]
    nlinarith [norm_nonneg x]
  · rw [show iteratedFDeriv ℝ (i + 1) (fun x => ph l c x - 1) x = _ from iteratedFDeriv_sub_apply
      ((ph_smooth l c).of_le (by exact_mod_cast le_top)).contDiffAt contDiffAt_const, iteratedFDeriv_succ_const]
    refine le_trans (by simpa using ph_bd l c (i + 1) x) ?_
    have : ‖l‖ ^ (i + 1) ≤ δ := (pow_le_of_le_one (norm_nonneg _) (hl.trans h1) (Nat.succ_ne_zero i)).trans hl
    nlinarith [norm_nonneg x]
end PositivityTheory.ThKCT.Arch
