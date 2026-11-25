-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicOnSubset_continuousWithinAt_trace_091da22534d2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:27:57.285237+00:00
-- url     : https://prove2.me/submissions/dc1091ab-899b-4a3b-bc3f-fc9597f25bc9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalTrace
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalBranchedCovering
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRiemannExtensionAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalTrace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial Topology Filter
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace HolomorphicOnSubset
theorem _root_.solution {σ : Type*} [Fintype σ] {g : (σ → ℂ) → ℂ}
    {S : Set (σ → ℂ)} (hg : HolomorphicOnSubset g S) {z : σ → ℂ} (hz : z ∈ S) :
    ContinuousWithinAt g S z := by
  obtain ⟨V, hV, hzV, F, hF, hgF⟩ := hg z hz
  have hFc : ContinuousAt F z := (hF.differentiableAt (hV.mem_nhds hzV)).continuousAt
  refine hFc.continuousWithinAt.congr_of_eventuallyEq ?_ (hgF ⟨hz, hzV⟩)
  filter_upwards [inter_mem_nhdsWithin S (hV.mem_nhds hzV)] with x hx using hgF hx
end HolomorphicOnSubset
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
