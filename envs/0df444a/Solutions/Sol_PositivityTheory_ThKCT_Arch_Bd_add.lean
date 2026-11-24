-- Prove2me | solution 1 for PositivityTheory.ThKCT.Arch.Bd.add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:56.174791+00:00
-- url     : https://prove2.me/submissions/6779855b-db93-41d1-b9bf-9b31ec434e04

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_SliceArch

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
namespace Bd
theorem _root_.solution {m : ℕ} {f g : V → ℂ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {C D : ℝ} (h : Bd m f C) (h' : Bd m g D) :
    Bd m (fun x => f x + g x) (C + D) := by
  intro j hj x
  rw [show iteratedFDeriv ℝ j (fun x => f x + g x) x = _ from iteratedFDeriv_add_apply
    (hf.of_le (by exact_mod_cast le_top)).contDiffAt (hg.of_le (by exact_mod_cast le_top)).contDiffAt]
  refine le_trans (mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)) ?_
  rw [mul_add]
  exact add_le_add (h j hj x) (h' j hj x)
end Bd
end PositivityTheory.ThKCT.Arch
