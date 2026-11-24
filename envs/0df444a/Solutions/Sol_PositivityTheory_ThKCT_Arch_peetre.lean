-- Prove2me | solution 1 for PositivityTheory.ThKCT.Arch.peetre
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:50.055812+00:00
-- url     : https://prove2.me/submissions/be9cc2bf-c38a-497c-bea1-b6648b565ee9

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
theorem _root_.solution (x y : V) {r : ℝ} (h : ‖y - x‖ ≤ r) : 1 + ‖x‖ ≤ (1 + r) * (1 + ‖y‖) := by
  have h1 : ‖x‖ ≤ ‖y‖ + ‖y - x‖ := by simpa using norm_sub_le y (y - x)
  nlinarith [norm_nonneg y, norm_nonneg (y - x)]
end PositivityTheory.ThKCT.Arch
