-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.HSt.MI.isOpen_Inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:40.649708+00:00
-- url     : https://prove2.me/submissions/e8148255-6d48-4ecf-ac25-1d3c0296998a

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IILeft
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_MatInv
import Theorems.Thm_PositivityTheory_Rg_Sw_HSt_MI_contDiff_det

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Set Filter Topology
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.HSt PositivityTheory.Rg.Sw.HSt.MI
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.HSt.MI
theorem _root_.solution : IsOpen (Inv n) := isOpen_ne_fun (contDiff_det.continuous) continuous_const
end PositivityTheory.Rg.Sw.HSt.MI
