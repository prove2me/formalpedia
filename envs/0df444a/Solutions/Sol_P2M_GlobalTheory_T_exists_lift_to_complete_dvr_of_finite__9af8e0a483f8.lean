-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_lift_to_complete_dvr_of_finite__9af8e0a483f8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:54:03.184216+00:00
-- url     : https://prove2.me/submissions/a33bb484-3052-465c-bc3b-f1911c8d38bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftToCompleteDvrOfFinite
import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GroupLattices_PerfectRings_IsLocalRingOfComplete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftToCompleteDvrOfFiniteStatement
import Theorems.Thm_GlobalTheory_exists_lift_to_complete_dvr_of_finite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A R : Type) [CommRing A] [CommRing R] [Algebra A R], Function.Injective (algebraMap A R) →
    Module.Finite A R → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (maximalIdeal V) V → ∀ h : A →+* V,
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : CharZero V')
      (f : V →+* V') (ρ : R →+* V'), IsAdicComplete (maximalIdeal V') V' ∧
      Function.Injective f ∧ IsLocalHom f ∧ ρ.comp (algebraMap A R) = f.comp h := by
  first | exact @GlobalTheory.exists_lift_to_complete_dvr_of_finite | exact GlobalTheory.exists_lift_to_complete_dvr_of_finite | (intros; apply GlobalTheory.exists_lift_to_complete_dvr_of_finite <;> assumption)
end _root_.GlobalTheory.T
