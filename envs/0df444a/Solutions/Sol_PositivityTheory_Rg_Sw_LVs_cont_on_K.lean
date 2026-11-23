-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.cont_on_K
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:49:53.663884+00:00
-- url     : https://prove2.me/submissions/44d0de7b-081d-4c6b-b4c0-c22790691ce2

import Mathlib
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZeroDimA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ScalarSectionCompactBlockInvariant
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFderivRightTranslation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Matrix
open scoped ContDiff
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs
open PositivityTheory.Rg.Sw
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution (H : M2 n → ℂ) (hH : ContDiffOn ℂ ∞ H (Dom n)) (Kg : Type) [TopologicalSpace Kg]
    (ι : Kg → M2 n) (hι : Continuous ι) (hdom : ∀ k, ι k ∈ Dom n) : Continuous (fun k => H (ι k)) :=
  hH.continuousOn.comp_continuous hι hdom
end PositivityTheory.Rg.Sw.LVs
