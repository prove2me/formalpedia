-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_pullback_map_injective_unit_98af568d62d2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:05:55.68681+00:00
-- url     : https://prove2.me/submissions/83d4b684-73e9-4fdc-8028-c768b047e83c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsPullbackFaithful
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PVectorBundleRestrict
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PPullbackFaithful

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
universe u
set_option backward.isDefEq.respectTransparency.types false
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution {T U : Scheme.{u}} (g : T ⟶ U)
    (hg : ∀ W : U.Opens, Function.Injective (g.app W)) {A : U.Modules}
    (φ₁ φ₂ : A ⟶ structureModule U)
    (h : (Scheme.Modules.pullback g).map φ₁ = (Scheme.Modules.pullback g).map φ₂) : φ₁ = φ₂ := by
  have : (SheafOfModules.pushforward g.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction g).isRightAdjoint
  have key : ∀ φ : A ⟶ structureModule U,
      ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _)
        ((Scheme.Modules.pullback g).map φ ≫
          SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) =
      φ ≫ SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom := by
    intro φ
    rw [Adjunction.homEquiv_naturality_left]
    congr 1
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _
  have h2 : φ₁ ≫ SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom =
      φ₂ ≫ SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom := by
    rw [← key, ← key, h]
  ext W x
  have := congr((($h2).app W).hom x)
  exact hg W this
end GroundTheory.Heights₂.Heights.Model
