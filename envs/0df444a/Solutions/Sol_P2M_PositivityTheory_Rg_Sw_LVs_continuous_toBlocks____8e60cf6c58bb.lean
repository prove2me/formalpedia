-- Prove2me | solution 1 for P2M_PositivityTheory_Rg_Sw_LVs_continuous_toBlocks____8e60cf6c58bb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:50:04.567234+00:00
-- url     : https://prove2.me/submissions/13b8d10e-b8a8-42d3-bb7a-648272878fe5

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SingToDiffAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_SecondCayleyBlockMulConjTransposeEq
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant

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
theorem _root_.solution : Continuous (fun x : M2 n => x.toBlocks₁₁) :=
  continuous_pi fun i => continuous_pi fun j => (continuous_apply (Sum.inl j)).comp (continuous_apply (Sum.inl i))
end PositivityTheory.Rg.Sw.LVs
