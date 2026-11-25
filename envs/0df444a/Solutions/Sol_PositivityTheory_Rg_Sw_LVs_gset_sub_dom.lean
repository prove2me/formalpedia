-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.gset_sub_dom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:17:22.486674+00:00
-- url     : https://prove2.me/submissions/e3d9e69d-1aa3-4f5c-92de-9558e34f5b87

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulConjTransposeEq
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_isUnit_det_of_inG__484f4d84a40f
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_det_first_cayley_block_ne_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_det_second_cayley_block_ne_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_inverse_first_block_eq_of_group


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
theorem _root_.solution : GSet n ⊆ Dom n := fun g hg => by
  refine ⟨isUnit_det_of_inG' hg, det_first_cayley_block_ne_zero hg, det_second_cayley_block_ne_zero hg, ?_⟩
  rw [inverse_first_block_eq_of_group hg, det_conjTranspose]
  exact star_ne_zero.2 (det_first_cayley_block_ne_zero hg)
end PositivityTheory.Rg.Sw.LVs
