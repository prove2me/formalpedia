-- Prove2me | solution 1 for PositivityTheory.ThKCT.Arch.sc_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:12.835044+00:00
-- url     : https://prove2.me/submissions/685ffb99-0c78-4656-85b7-367544c55cb1

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
theorem _root_.solution {Z : Type} [AddCommGroup Z] [Module ℂ Z] {C : ℝ} (h : 0 ≤ C) (p : Seminorm ℂ Z) (f : Z) : sc C p f = C * p f := by
  rw [sc, Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ h]
end PositivityTheory.ThKCT.Arch
