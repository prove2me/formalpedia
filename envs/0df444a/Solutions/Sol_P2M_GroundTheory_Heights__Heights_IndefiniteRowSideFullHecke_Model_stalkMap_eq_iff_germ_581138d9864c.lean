-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_stalkMap_eq_iff_germ_581138d9864c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:10:06.810174+00:00
-- url     : https://prove2.me/submissions/db084c62-b342-4360-ad7d-22623ee21dd6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_GenericImageEqGermImage

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
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
noncomputable section
universe u
variable {X : Scheme.{u}}
variable [IrreducibleSpace X]
variable {E E' : X.Modules}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
theorem _root_.solution (ψ : E ≅ E')
    (f : E.presheaf.stalk (genericPoint X) → E'.presheaf.stalk (genericPoint X)) :
    (∀ v, ((TopCat.Presheaf.stalkFunctor Ab (genericPoint X)).map
      (Scheme.Modules.Hom.mapPresheaf ψ.hom)).hom v = f v) ↔
    ∀ (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(E, U)),
      f (E.presheaf.germ U _ hU s) = E'.presheaf.germ U _ hU (Scheme.Modules.Hom.app ψ.hom U s) := by
  constructor
  · intro h U hU s
    exact (h _).symm.trans (TopCat.Presheaf.stalkFunctor_map_germ_apply U _ hU _ s)
  · intro h v
    obtain ⟨U, hU, s, rfl⟩ := E.presheaf.exists_germ_eq v
    exact (TopCat.Presheaf.stalkFunctor_map_germ_apply U _ hU _ s).trans (h U hU s).symm
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
