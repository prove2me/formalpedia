-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_ClearDenominators_hypotheses_inhabited_3b7af47caf18
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:24:59.663887+00:00
-- url     : https://prove2.me/submissions/0ee7f6b8-7af1-4342-b5e4-e231194e1f23

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_isVectorBundle_structureModule_93a0cef3461d

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
namespace ClearDenominators
theorem _root_.solution :
    Flat (𝟙 SpecZ) ∧ CompactSpace SpecZ ∧ QuasiSeparatedSpace SpecZ ∧
      IsVectorBundle (structureModule SpecZ) :=
  ⟨inferInstance, inferInstance, inferInstance, isVectorBundle_structureModule⟩
end ClearDenominators
end GroundTheory.Heights₂.Heights.Model
