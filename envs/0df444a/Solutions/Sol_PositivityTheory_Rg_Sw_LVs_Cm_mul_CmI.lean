-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.Cm_mul_CmI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:55:38.848811+00:00
-- url     : https://prove2.me/submissions/1768fb82-ae2c-4881-a38f-93486722b3d2

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_DpDual
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_isUnit_det_Cm
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_dp_Cm_inv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open scoped ContDiff ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PositivityTheory.Rg.Sw
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution : Cm n * CmI n = 1 := by
  rw [← dp_Cm_inv]; exact Matrix.mul_nonsing_inv _ isUnit_det_Cm
end PositivityTheory.Rg.Sw.LVs
