-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_UniformiserLocallyInjective_proof_1e212993bea7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:11:33.167466+00:00
-- url     : https://prove2.me/submissions/c1dc9a0c-6a55-424d-9b83-c9b750506025

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUniformiserLocallyInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StUniformiserGradientIndependent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPolynomialChartInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PUniformiserLocallyInjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Topology
namespace GroundTheory.Heights₂.Heights
namespace UniformiserLocallyInjective
theorem _root_.solution (hgrad : UniformiserGradientIndependent.Statement)
    (hchart : PolynomialChartInjective.Statement) : UniformiserLocallyInjective.Statement := by
  intro σ _ I w t hI hic hdim hw ht
  obtain ⟨k, f, hk, hfI, hli⟩ := hgrad σ I w t hI hic hdim hw ht
  obtain ⟨U, hU, hinj⟩ := hchart σ k t f w hk hli
  refine ⟨U, hU, hinj.mono ?_⟩
  rintro z ⟨hz, hzU⟩
  exact ⟨hzU, fun j ↦ hz (f j) (hfI j)⟩
end UniformiserLocallyInjective
end GroundTheory.Heights₂.Heights
