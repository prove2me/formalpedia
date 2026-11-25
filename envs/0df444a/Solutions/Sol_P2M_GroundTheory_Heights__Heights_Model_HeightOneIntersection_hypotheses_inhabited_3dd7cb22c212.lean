-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_HeightOneIntersection_hypotheses_inhabited_3dd7cb22c212
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:04:58.938873+00:00
-- url     : https://prove2.me/submissions/de138955-123d-4d52-b27f-df620ee2c8d3

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
namespace HeightOneIntersection
theorem _root_.solution :
    IsNoetherianRing ℤ ∧ IsIntegrallyClosed ℤ ∧ IsFractionRing ℤ ℚ :=
  ⟨inferInstance, inferInstance, inferInstance⟩
end HeightOneIntersection
end GroundTheory.Heights₂.Heights.Model
