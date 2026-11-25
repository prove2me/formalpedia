-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.Cm_mul_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:57:23.718155+00:00
-- url     : https://prove2.me/submissions/9b6b62c1-13aa-48bb-ac24-41623fecd442

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContDiffOnSecondCayleyBlockEntries
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_Cm_mul_Cinv
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_Cm_inv__b2da14

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
theorem _root_.solution : Cm n * (Cm n)⁻¹ = 1 := by rw [Cm_inv]; exact Cm_mul_Cinv
end PositivityTheory.Rg.Sw.LVs
