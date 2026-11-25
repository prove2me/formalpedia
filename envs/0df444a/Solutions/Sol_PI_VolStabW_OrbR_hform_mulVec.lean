-- Prove2me | solution 1 for PI.VolStabW.OrbR.hform_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:56:33.27946+00:00
-- url     : https://prove2.me/submissions/9fdb15fc-4e42-417c-8276-20f5f2945cf9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_HformEntry
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_OrbRing
import Theorems.Thm_PIW_AdelicOrbitU_hform_eq_dot


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW PI.VolStabW.OrbR
open Matrix Formalism.UG PIW.AdelicOrbitU
variable {S : Type} [CommRing S] (s : S →+* S) {n : ℕ} (J : Matrix (Fin n) (Fin n) S)
namespace PI.VolStabW.OrbR
theorem _root_.solution (T : Matrix (Fin n) (Fin n) S) (z w : Fin n → S) :
    hform s J (T *ᵥ z) (T *ᵥ w) = hform s (cT s T * J * T) z w := by
  rw [hform_eq_dot, hform_eq_dot]
  have e : (fun i => s ((T *ᵥ z) i)) = T.map s *ᵥ (fun i => s (z i)) := by
    funext i; exact RingHom.map_mulVec s T z i
  rw [e, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec]
  rfl
end PI.VolStabW.OrbR
