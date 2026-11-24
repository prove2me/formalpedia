-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicOnSubset_continuousWithinAt_7f073503ccef
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:11.363794+00:00
-- url     : https://prove2.me/submissions/e176111d-756d-4ab1-b584-8af5cec59dfe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchContainsNormalPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalLocallyIrreducible
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicOnSubset
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBranchInverseHolomorphic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalRiemannExtension
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalMaximumPrinciple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PBranchContainsNormalPoint

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
open MvPolynomial Filter Topology
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace HolomorphicOnSubset
theorem _root_.solution {σ : Type*} [Fintype σ] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {f : (σ → ℂ) → E} {S : Set (σ → ℂ)}
    (hf : HolomorphicOnSubset f S) {z : σ → ℂ} (hz : z ∈ S) : ContinuousWithinAt f S z := by
  obtain ⟨U, hUo, hzU, F, hF, hFeq⟩ := hf z hz
  have hc : ContinuousWithinAt F S z :=
    (hF.differentiableAt (hUo.mem_nhds hzU)).continuousAt.continuousWithinAt
  refine hc.congr_of_eventuallyEq ?_ (hFeq ⟨hz, hzU⟩)
  filter_upwards [inter_mem_nhdsWithin S (hUo.mem_nhds hzU)] with y hy
  exact hFeq hy
end HolomorphicOnSubset
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
