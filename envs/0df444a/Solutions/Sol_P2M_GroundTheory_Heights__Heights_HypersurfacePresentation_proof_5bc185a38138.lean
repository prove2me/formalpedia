-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_proof_5bc185a38138
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:57:34.763747+00:00
-- url     : https://prove2.me/submissions/5aaff9bb-19f7-4314-953c-2e0e653be905

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHypersurfacePresentation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericPrimitive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PHypersurfacePresentation
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HypersurfacePresentation_hypersurfacePresentation_of_b39368514445

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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace HypersurfacePresentation
theorem _root_.solution : HypersurfacePresentation.Statement := by
  intro σ _ ι _ K hK hKS
  exact HypersurfacePresentation.hypersurfacePresentation_of K hKS
end HypersurfacePresentation
end GroundTheory.Heights₂.Heights
