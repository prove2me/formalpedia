-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_BundlesAgree_hypotheses_inhabited_1f0479b43ccd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:42:05.407452+00:00
-- url     : https://prove2.me/submissions/a2b09298-55fb-45b8-8d01-11a2e19f2588

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_isVectorBundle_structureModule_93a0cef3461d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_isNormalScheme_specZ_75d583b78156

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
namespace BundlesAgree
theorem _root_.solution :
    IsIntegral SpecZ ∧ IsLocallyNoetherian SpecZ ∧ IsNormalScheme SpecZ ∧
      IsVectorBundle (structureModule SpecZ) ∧
      ∀ x : SpecZ, ringKrullDim (SpecZ.presheaf.stalk x) = 1 →
        (genericImage (structureModule SpecZ) x).map
          (LinearEquiv.refl (SpecZ.presheaf.stalk (genericPoint SpecZ))
            ((structureModule SpecZ).presheaf.stalk (genericPoint SpecZ))).toAddMonoidHom =
          genericImage (structureModule SpecZ) x :=
  ⟨inferInstance, inferInstance, isNormalScheme_specZ, isVectorBundle_structureModule,
    fun _ _ => AddSubgroup.map_id _⟩
end BundlesAgree
end GroundTheory.Heights₂.Heights.Model
