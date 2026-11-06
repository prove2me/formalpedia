-- Prove2me | solution 1 for QEC.Semantics.QuditSubsystem.fullRegion_extension_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T12:31:06.16742+00:00
-- url     : https://prove2.me/submissions/56cb9285-cbb5-4c8b-b3f4-823243fa835e

import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditNoInformation
import Definitions.Def_QEC_Semantics_ErrorCorrection_FiniteMeasurementDistance
import Theorems.Thm_QEC_Semantics_QuditSubsystem_extendLocalToRegister_injective


set_option autoImplicit false
noncomputable section
open QEC QEC.Semantics QEC.Semantics.QuditSubsystem
open scoped BigOperators
universe u
variable {J : Type u} [Fintype J] [DecidableEq J] (q : J → Nat)
namespace QEC.Semantics.QuditSubsystem
theorem _root_.solution (hq : ∀ j, 0 < q j) :
    Function.Surjective (fullRegion q).extendLocalToRegister := by
  have hd : Module.finrank Complex (fullRegion q).selectedSystem =
      Module.finrank Complex (Qudit.QuditRegister q) := by
    rw [finrank_euclideanSpace, finrank_euclideanSpace]
    exact Fintype.card_congr (fullRegionLabelEquiv q)
  have he : Module.finrank Complex (Operator (fullRegion q).selectedSystem) =
      Module.finrank Complex (Operator (Qudit.QuditRegister q)) := by
    change Module.finrank Complex ((fullRegion q).selectedSystem →ₗ[Complex]
      (fullRegion q).selectedSystem) =
      Module.finrank Complex (Qudit.QuditRegister q →ₗ[Complex] Qudit.QuditRegister q)
    rw [Module.finrank_linearMap, Module.finrank_linearMap, hd]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank he
    (f := extensionLinearMap q (fullRegion q))).mp
      ((fullRegion q).extendLocalToRegister_injective hq)
end QEC.Semantics.QuditSubsystem
