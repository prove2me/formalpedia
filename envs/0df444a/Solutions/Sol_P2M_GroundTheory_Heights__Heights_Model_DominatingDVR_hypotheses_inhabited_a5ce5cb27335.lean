-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_DominatingDVR_hypotheses_inhabited_a5ce5cb27335
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:25:12.208802+00:00
-- url     : https://prove2.me/submissions/905343b3-2576-4d9c-8a28-752ee9c58a53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open NumbersDVR ReciprocityTheory.ChartRestriction.G.Geo
namespace GroundTheory.Heights₂.Heights.Model
namespace DominatingDVR
theorem _root_.solution :
    IsDomain ℤ_[2] ∧ IsNoetherianRing ℤ_[2] ∧ IsLocalRing ℤ_[2] ∧ ¬ IsField ℤ_[2] ∧
      IsFractionRing ℤ_[2] ℚ_[2] :=
  ⟨inferInstance, inferInstance, inferInstance, IsDiscreteValuationRing.not_isField _,
    inferInstance⟩
end DominatingDVR
end GroundTheory.Heights₂.Heights.Model
