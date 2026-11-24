-- Prove2me | solution 1 for PositivityTheory.ThKCT.Arch.shift_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:50.467396+00:00
-- url     : https://prove2.me/submissions/546bb70d-c945-486f-9043-d20ec3c5dab5

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_SliceArch
import Theorems.Thm_PositivityTheory_ThKCT_Arch_Bd_add

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
theorem _root_.solution (f : SchwartzMap V ℂ) (t : V) : ContDiff ℝ ∞ fun x => f (x + t) :=
  (f.smooth ⊤).comp (contDiff_id.add contDiff_const)
end PositivityTheory.ThKCT.Arch
