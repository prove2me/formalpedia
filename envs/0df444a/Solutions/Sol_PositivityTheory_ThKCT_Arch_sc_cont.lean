-- Prove2me | solution 1 for PositivityTheory.ThKCT.Arch.sc_cont
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:13.050819+00:00
-- url     : https://prove2.me/submissions/c395a921-65fd-407f-89f3-0164408138d8

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
theorem _root_.solution {Z : Type} [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z] (C : ℝ) {p : Seminorm ℂ Z} (h : Continuous p) :
    Continuous (sc C p) := ((continuous_const (y := (C.toNNReal : ℝ))).mul h).congr fun f => by
  rw [sc, Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul]; rfl
end PositivityTheory.ThKCT.Arch
