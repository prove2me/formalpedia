-- Prove2me | solution 1 for PI.VolStabSW.OrbR.hform_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:09:32.891825+00:00
-- url     : https://prove2.me/submissions/523a0b8f-f23c-49fd-b4d0-5dc790b7642b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_HformEntry
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_OrbRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
namespace PI.VolStabSW.OrbR
open Matrix Formalism.UG PIW.AdelicOrbitU
variable {S : Type} [CommRing S] (s : S →+* S) {n : ℕ} (J : Matrix (Fin n) (Fin n) S)
private lemma hform_eq_lemma (M : Matrix (Fin n) (Fin n) S) (u z : Fin n → S) :
    hform s M u z = (fun i => s (u i)) ⬝ᵥ (M *ᵥ z) := by
  simp only [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
end PI.VolStabSW.OrbR
end
end

set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.OrbR
open Matrix Formalism.UG PIW.AdelicOrbitU
variable {S : Type} [CommRing S] (s : S →+* S) {n : ℕ} (J : Matrix (Fin n) (Fin n) S)
namespace PI.VolStabSW.OrbR
theorem _root_.solution (T : Matrix (Fin n) (Fin n) S) (z w : Fin n → S) :
    hform s J (T *ᵥ z) (T *ᵥ w) = hform s (cT s T * J * T) z w := by
  rw [hform_eq_lemma, hform_eq_lemma]
  have e : (fun i => s ((T *ᵥ z) i)) = (T.map s) *ᵥ (fun i => s (z i)) := by
    funext i
    exact RingHom.map_mulVec s T z i
  rw [e]
  unfold cT
  calc (T.map s *ᵥ fun i => s (z i)) ⬝ᵥ (J *ᵥ (T *ᵥ w))
      = ((J *ᵥ (T *ᵥ w)) ᵥ* (T.map s)) ⬝ᵥ (fun i => s (z i)) := by
        rw [dotProduct_comm, dotProduct_mulVec]
    _ = (fun i => s (z i)) ⬝ᵥ ((T.map s)ᵀ *ᵥ (J *ᵥ (T *ᵥ w))) := by
        rw [dotProduct_comm, mulVec_transpose]
    _ = (fun i => s (z i)) ⬝ᵥ (((T.map s)ᵀ * J * T) *ᵥ w) := by
        simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
end PI.VolStabSW.OrbR
