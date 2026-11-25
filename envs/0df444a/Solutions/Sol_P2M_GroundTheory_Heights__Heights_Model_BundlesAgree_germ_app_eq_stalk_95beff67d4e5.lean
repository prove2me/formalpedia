-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_BundlesAgree_germ_app_eq_stalk_95beff67d4e5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:24:50.783469+00:00
-- url     : https://prove2.me/submissions/1dbab78e-493c-47e4-b6a6-a356a4868524

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGenericGerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsHeightOneSections
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PBundlesAgree

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
open GroundTheory.Heights₂.Heights.Model.BundlesAgree
variable {X : Scheme.{0}} [IsIntegral X]
variable (E E' : X.Modules)
  (φ : E.presheaf.stalk (genericPoint X) →ₗ[X.presheaf.stalk (genericPoint X)]
    E'.presheaf.stalk (genericPoint X))
  (hex : ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(E, U)), ∃ t : Γ(E', U),
    E'.presheaf.germ U (genericPoint X) hU t = φ (E.presheaf.germ U (genericPoint X) hU s))
  (hE' : ∀ (U : X.Opens) (hU : genericPoint X ∈ U),
      Function.Injective (E'.presheaf.germ U (genericPoint X) hU))
omit [IsIntegral X]
namespace GroundTheory.Heights₂.Heights.Model.BundlesAgree
theorem _root_.solution (f : E ⟶ E') (U : X.Opens) (x : X) (hU : x ∈ U) (s : Γ(E, U)) :
    E'.presheaf.germ U x hU (f.app U s) =
      ((TopCat.Presheaf.stalkFunctor Ab x).map (Scheme.Modules.Hom.mapPresheaf f)).hom
        (E.presheaf.germ U x hU s) := by
  have := TopCat.Presheaf.stalkFunctor_map_germ_apply (F := E.presheaf) (G := E'.presheaf) U x hU
    (Scheme.Modules.Hom.mapPresheaf f) s
  exact this.symm
end GroundTheory.Heights₂.Heights.Model.BundlesAgree
