-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_LelongWeightDiff_tendsto_finset_sum_zero_a6939454619a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T05:21:28.890227+00:00
-- url     : https://prove2.me/submissions/e8f85126-8cdf-4a01-89c1-056775fd6491

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StLelongWeightDiff
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCutOffDominated
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PLelongWeightDiffLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open GroundTheory.Heights₂.Heights.Targets.LelongWeightDiff
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.Targets.LelongWeightDiff
theorem _root_.solution {ι α : Type*} {l : Filter α} (s : Finset ι) (f : ι → α → ℝ)
    (h : ∀ i ∈ s, Tendsto (f i) l (𝓝 0)) : Tendsto (fun a => ∑ i ∈ s, f i a) l (𝓝 0) := by
  simpa using tendsto_finsetSum s h
end GroundTheory.Heights₂.Heights.Targets.LelongWeightDiff
