-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_BundlesAgree_germ_homOfGeneric_app_ae35dc9a743d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:24:54.284633+00:00
-- url     : https://prove2.me/submissions/67a97897-4030-49e6-b7b2-56d5b373ba2f

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
include hE'
namespace GroundTheory.Heights₂.Heights.Model.BundlesAgree
theorem _root_.solution (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(E, U)) :
    E'.presheaf.germ U (genericPoint X) hU ((homOfGeneric E E' φ hex hE').app U s) =
      φ (E.presheaf.germ U (genericPoint X) hU s) :=
  germ_lift E E' φ hex U hU s
end GroundTheory.Heights₂.Heights.Model.BundlesAgree
