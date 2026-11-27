-- Prove2me | solution 1 for PositivityTheory.ThKCT.Arch.S_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:20:46.345409+00:00
-- url     : https://prove2.me/submissions/c558eb8c-5560-4591-9dcd-b0816f1c46b0

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_SliceArch
import Theorems.Thm_PositivityTheory_ThKCT_Arch_S_zero
import Theorems.Thm_PositivityTheory_ThKCT_Arch_S_add

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
theorem _root_.solution (w : V × (V →L[ℝ] ℝ)) (f : SchwartzMap V ℂ) : S w (S (-w) f) = f := by
  have := S_add w (-w) f
  rw [add_neg_cancel, S_zero] at this
  simpa using this.symm
end PositivityTheory.ThKCT.Arch
