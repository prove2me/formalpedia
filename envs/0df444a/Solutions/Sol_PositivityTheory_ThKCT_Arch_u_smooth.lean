-- Prove2me | solution 1 for PositivityTheory.ThKCT.Arch.u_smooth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:39.352251+00:00
-- url     : https://prove2.me/submissions/da5681c9-3242-457b-bc39-fec0792b1586

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_SmallCones_SliceArch
import Theorems.Thm_PositivityTheory_ThKCT_Arch_Bd_mul
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
theorem _root_.solution (c : ℝ) : ContDiff ℝ ∞ fun s : ℝ => cexp (I * ((s + c : ℝ) : ℂ)) :=
  (contDiff_const.mul (ofRealCLM.contDiff.comp (contDiff_id.add contDiff_const))).cexp
end PositivityTheory.ThKCT.Arch
