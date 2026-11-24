-- Prove2me | solution 1 for PositivityTheory.ThKCT.Arch.Bd.nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:04.591172+00:00
-- url     : https://prove2.me/submissions/3e0433d4-6168-4704-a5a3-348ecec6546a

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
theorem _root_.solution {m : ℕ} {f : V → ℂ} {C : ℝ} (h : Bd m f C) : 0 ≤ C :=
  le_trans (by positivity) (h 0 (Nat.zero_le _) 0)
end Bd
end PositivityTheory.ThKCT.Arch
