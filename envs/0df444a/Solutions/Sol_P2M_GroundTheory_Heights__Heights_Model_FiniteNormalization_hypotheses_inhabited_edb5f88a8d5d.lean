-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_FiniteNormalization_hypotheses_inhabited_edb5f88a8d5d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:04:45.380871+00:00
-- url     : https://prove2.me/submissions/587b02b3-513b-4e95-849f-bbc4b07d3032

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
namespace FiniteNormalization
theorem _root_.solution :
    IsIntegral SpecZ ∧ LocallyOfFiniteType (𝟙 SpecZ) ∧ QuasiCompact (𝟙 SpecZ) ∧
      FiniteDimensional SpecZ.functionField SpecZ.functionField :=
  ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
end FiniteNormalization
end GroundTheory.Heights₂.Heights.Model
