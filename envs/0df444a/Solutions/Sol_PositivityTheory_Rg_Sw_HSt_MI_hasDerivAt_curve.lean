-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.HSt.MI.hasDerivAt_curve
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:02:14.545808+00:00
-- url     : https://prove2.me/submissions/f51ec41f-fa9c-4ef2-9a50-333e6c80329d

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IILeft
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_CayleyCosetSums_MatInv
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_cE_hasDerivAt0
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_II_mulL_apply


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
theorem _root_.solution (x Z : M2 n) :
    HasDerivAt (fun t : ℝ => x * NormedSpace.exp ((t : ℂ) • Z)) (x * Z) 0 := by
  have h0 := LVs.II.cE_hasDerivAt0 Z
  have h1 := (LVs.II.mulL x).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h0
  refine h1.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
  simp [Function.comp_def, LVs.II.mulL_apply, LVs.II.cE, Complex.coe_smul]
end PositivityTheory.Rg.Sw.HSt.MI
