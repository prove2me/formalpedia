-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_BundlesAgree_hom_ext_of_germ_e9a54a5bbb2d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:24:57.965188+00:00
-- url     : https://prove2.me/submissions/cd52f6d5-ea0f-4a68-b8dd-86897f7e0714

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
theorem _root_.solution {f g : E ⟶ E'}
    (h : ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(E, U)),
      E'.presheaf.germ U (genericPoint X) hU (f.app U s) =
        E'.presheaf.germ U (genericPoint X) hU (g.app U s)) : f = g :=
  Scheme.Modules.hom_ext f g fun U => by
    ext s
    exact section_ext E' hE' fun hU => h U hU s
end GroundTheory.Heights₂.Heights.Model.BundlesAgree
