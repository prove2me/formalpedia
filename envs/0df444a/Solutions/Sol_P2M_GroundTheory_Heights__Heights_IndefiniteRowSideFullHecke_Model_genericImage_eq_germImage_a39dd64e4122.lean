-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_genericImage_eq_germImage_a39dd64e4122
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:33:17.472867+00:00
-- url     : https://prove2.me/submissions/9d22a0c7-fd34-4493-8783-99cea6387b8b

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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
theorem _root_.solution (E : X.Modules) (x : X) :
    (GroundTheory.Heights₂.Heights.Model.genericImage E x : Set (E.presheaf.stalk (genericPoint X))) =
      germImage E x := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨U, hxU, s, rfl⟩ := E.presheaf.exists_germ_eq w
    exact ⟨U, hxU, (genericPoint_specializes x).mem_open U.isOpen hxU, s,
      (E.presheaf.germ_stalkSpecializes_apply hxU (genericPoint_specializes x) s).symm⟩
  · rintro ⟨U, hxU, hU, s, rfl⟩
    exact ⟨E.presheaf.germ U x hxU s, E.presheaf.germ_stalkSpecializes_apply hxU _ s⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
