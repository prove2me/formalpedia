-- Prove2me | solution 1 for PositivityTheory.ThKCT.Arch.Bd.mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:20:42.412376+00:00
-- url     : https://prove2.me/submissions/217315ea-153e-453d-b482-b481f2d679c4

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
theorem _root_.solution {m : ℕ} {f : V → ℂ} {C C' : ℝ} (h : Bd m f C) (hC : C ≤ C') : Bd m f C' :=
  fun j hj x => (h j hj x).trans hC
end Bd
end PositivityTheory.ThKCT.Arch
