-- Prove2me | solution 1 for PositivityTheory.ThKCT.Arch.P_cont
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:55.548505+00:00
-- url     : https://prove2.me/submissions/f66afa3b-7e3a-4c41-b222-2f076669fa09

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
theorem _root_.solution (m : ℕ) : Continuous (P V m) :=
  Seminorm.continuous_finsetSup fun i _ => (schwartz_withSeminorms ℂ V ℂ).continuous_seminorm i
end PositivityTheory.ThKCT.Arch
