-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.fV_law
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:22:11.195938+00:00
-- url     : https://prove2.me/submissions/021505d7-307f-4c7b-804d-20cd937b6b1b

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulConjTransposeEq
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
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
theorem _root_.solution (p q : ℤ) {P x : M2 n} (hP : InP P) (hx : x ∈ Dom n) :
    fV p q (P * x) = c2 p q P * fV p q x := by
  simp only [fV, c2, automorphy_first_mul_parabolic x hP.2, automorphy_second_mul_parabolic x hP.2, inverse_first_block_mul_parabolic hP.2 (isUnit_det_of_inG' hP.1), det_mul,
    det_nonsing_inv, Ring.inverse_eq_inv', mul_zpow, _root_.inv_zpow', neg_neg, zpow_natCast]
  ring
end PositivityTheory.Rg.Sw.LVs
