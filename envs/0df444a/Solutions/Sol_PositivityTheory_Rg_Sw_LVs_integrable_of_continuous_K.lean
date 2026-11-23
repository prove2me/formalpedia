-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LVs.integrable_of_continuous_K
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:53:49.514389+00:00
-- url     : https://prove2.me/submissions/0e7482cc-db00-4917-9950-c38428e4b753

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_ContinuousOnIteratedFDerivTranslate
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_AnalyticDeterminants_IteratedFDerivMulConstOf

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
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.LVs
theorem _root_.solution {Kg : Type} [TopologicalSpace Kg] [CompactSpace Kg] [MeasurableSpace Kg]
    [BorelSpace Kg] (μ : Measure Kg) [IsFiniteMeasureOnCompacts μ] {f : Kg → ℂ} (hf : Continuous f) :
    Integrable f μ :=
  hf.integrable_of_hasCompactSupport (IsCompact.of_isClosed_subset isCompact_univ (isClosed_tsupport f) (Set.subset_univ _))
end PositivityTheory.Rg.Sw.LVs
