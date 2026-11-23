-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.continuousOn_wM
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:55:57.638585+00:00
-- url     : https://prove2.me/submissions/046a1eb2-c793-48ae-b697-86911556de29

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulConjTransposeEq
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_continuous_first_cayley_block_map
import Theorems.Thm_PositivityTheory_Rg_Sw_LVs_continuous_second_cayley_block_map
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
theorem _root_.solution : ContinuousOn (fun x : M2 n => wM x) {x | (u2 x).det ≠ 0} := by
  have h : ContinuousOn (fun x : M2 n => (u2 x)⁻¹) {x | (u2 x).det ≠ 0} :=
    continuousOn_inv'.comp continuous_second_cayley_block_map.continuousOn fun x hx => hx
  exact h.mul continuous_first_cayley_block_map.continuousOn
end PositivityTheory.Rg.Sw.LVs
