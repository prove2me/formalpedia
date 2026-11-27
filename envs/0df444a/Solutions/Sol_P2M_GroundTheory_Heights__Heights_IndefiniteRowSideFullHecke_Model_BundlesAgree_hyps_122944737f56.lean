-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_BundlesAgree_hyps_122944737f56
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:59:18.737123+00:00
-- url     : https://prove2.me/submissions/b039d0f7-7874-4a4a-b119-f6c2be856828

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleSheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_WeilDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_isNormalScheme_specInt_f10714e7ae74

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
open CategoryTheory Opposite AlgebraicGeometry Limits TopologicalSpace MonoidalCategory
open GroundTheory.Arith.SchemeCoh
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
namespace BundlesAgree
theorem _root_.solution :
    IsIntegral specInt ∧ IsNormalScheme specInt ∧ IsLocallyNoetherian specInt ∧
    IsVectorBundle (𝟙_ specInt.Modules) ∧
    ∀ x : specInt, ringKrullDim (specInt.presheaf.stalk x) = 1 →
      (GenericStalkIso.refl (𝟙_ specInt.Modules)).toAddEquiv '' germImage (𝟙_ specInt.Modules) x =
        germImage (𝟙_ specInt.Modules) x :=
  ⟨inferInstance, isNormalScheme_specInt, inferInstance, isVectorBundle_unit _,
    fun _ _ => Set.image_id _⟩
end BundlesAgree
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
