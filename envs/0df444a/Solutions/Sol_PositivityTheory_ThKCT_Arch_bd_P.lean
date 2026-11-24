-- Prove2me | solution 1 for PositivityTheory.ThKCT.Arch.bd_P
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:49.449977+00:00
-- url     : https://prove2.me/submissions/76e13f31-2524-431b-ae82-928c80e3c702

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
theorem _root_.solution (m : ℕ) (f : SchwartzMap V ℂ) : Bd m f (2 ^ m * P V m f) := fun j hj x =>
  SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (m, m)) le_rfl hj f x
end PositivityTheory.ThKCT.Arch
