-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.Cm_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:46:28.010874+00:00
-- url     : https://prove2.me/submissions/f28d8da3-1267-4895-b7a3-86c40e2a8981

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContDiffOnSecondCayleyBlockEntries
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_Cm_mul_Cinv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution : (Cm n)⁻¹ = Cinv n := Matrix.inv_eq_right_inv Cm_mul_Cinv
end PositivityTheory.Rg.Sw.LVs
