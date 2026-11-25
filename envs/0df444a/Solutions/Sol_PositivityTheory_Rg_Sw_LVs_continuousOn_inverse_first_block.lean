-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.continuousOn_inverse_first_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:02:33.895017+00:00
-- url     : https://prove2.me/submissions/274325fa-2437-42c2-9230-04d293c6e6aa

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulConjTransposeEq
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_continuous_toBlocks____fb38dccd8d2c
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_continuous_toBlocks____8e60cf6c58bb
import Theorems.Thm_P2M_PositivityTheory_Rg_Sw_LVs_continuousOn_inv__7715fb95dd1b

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
theorem _root_.solution : ContinuousOn (fun x : M2 n => ub1 x) {x | x.det ≠ 0} := by
  have h1 : ContinuousOn (fun x : M2 n => x⁻¹) {x | x.det ≠ 0} := continuousOn_inv'
  have h11 : ContinuousOn (fun x : M2 n => x⁻¹.toBlocks₁₁) {x | x.det ≠ 0} :=
    (continuous_toBlocks₁₁' (n := n)).comp_continuousOn h1
  have h21 : ContinuousOn (fun x : M2 n => x⁻¹.toBlocks₂₁) {x | x.det ≠ 0} :=
    (continuous_toBlocks₂₁' (n := n)).comp_continuousOn h1
  show ContinuousOn (fun x : M2 n => x⁻¹.toBlocks₁₁ + Complex.I • x⁻¹.toBlocks₂₁) _
  refine ContinuousOn.add h11 ?_
  exact fun x hx => (h21 x hx).const_smul Complex.I
end PositivityTheory.Rg.Sw.LVs
