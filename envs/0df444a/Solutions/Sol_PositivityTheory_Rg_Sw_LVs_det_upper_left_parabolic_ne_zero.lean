-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.det_upper_left_parabolic_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:48:34.81881+00:00
-- url     : https://prove2.me/submissions/e365dd51-4b70-4ccd-9f27-54ee12702da1

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulConjTransposeEq
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_isUnit_det_of_inG__484f4d84a40f
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_det_par


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
open scoped ComplexOrder
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {P : M2 n} (hP : InP P) : P.toBlocks₁₁.det ≠ 0 := by
  have h := isUnit_det_of_inG' hP.1
  rw [det_par hP.2] at h
  exact (isUnit_of_mul_isUnit_left h).ne_zero
end PositivityTheory.Rg.Sw.LVs
