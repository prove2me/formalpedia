-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.mul_mem_dom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:56:03.613142+00:00
-- url     : https://prove2.me/submissions/896bf948-a7db-4745-a4a7-912af20cd488

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulConjTransposeEq
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_det_lower_right_parabolic_ne_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_det_upper_left_parabolic_ne_zero
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_isUnit_det_of_inG__484f4d84a40f
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_automorphy_first_mul_parabolic
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_automorphy_second_mul_parabolic
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_inverse_first_block_mul_parabolic


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
theorem _root_.solution {P x : M2 n} (hP : InP P) (hx : x ∈ Dom n) : P * x ∈ Dom n := by
  obtain ⟨h0, h1, h2, h3⟩ := hx
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [det_mul]; exact (isUnit_det_of_inG' hP.1).mul h0
  · rw [automorphy_first_mul_parabolic x hP.2, det_mul]; exact mul_ne_zero (det_lower_right_parabolic_ne_zero hP) h1
  · rw [automorphy_second_mul_parabolic x hP.2, det_mul]; exact mul_ne_zero (det_lower_right_parabolic_ne_zero hP) h2
  · rw [inverse_first_block_mul_parabolic hP.2 (isUnit_det_of_inG' hP.1), det_mul, det_nonsing_inv, Ring.inverse_eq_inv']
    exact mul_ne_zero h3 (inv_ne_zero (det_upper_left_parabolic_ne_zero hP))
end PositivityTheory.Rg.Sw.LVs
