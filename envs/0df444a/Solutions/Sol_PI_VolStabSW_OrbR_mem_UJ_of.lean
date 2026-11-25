-- Prove2me | solution 1 for PI.VolStabSW.OrbR.mem_UJ_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:00:59.781806+00:00
-- url     : https://prove2.me/submissions/b9c6f3b7-9a6f-4ab0-92f1-5e330cc9009d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_HformEntry
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_OrbRing
import Theorems.Thm_PI_VolStabSW_OrbR_hform_mulVec
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
private lemma hform_single_single_stabilizer_orbit_volume (M : Matrix (Fin n) (Fin n) S) (a b : Fin n) :
    hform s M (Pi.single a 1) (Pi.single b 1) = M a b := by
  simp [hform, Pi.single_apply, apply_ite s]
end PI.VolStabSW.OrbR
end
end

set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.OrbR
open Matrix Formalism.UG PIW.AdelicOrbitU
variable {S : Type} [CommRing S] (s : S →+* S) {n : ℕ} (J : Matrix (Fin n) (Fin n) S)
namespace PI.VolStabSW.OrbR
theorem _root_.solution (hdet : IsUnit J.det) (T : Matrix (Fin n) (Fin n) S)
    (key : ∀ z w, hform s J (T *ᵥ z) (T *ᵥ w) = hform s J z w) :
    ∃ g : GL (Fin n) S, g ∈ UJ s J ∧ (g : Matrix (Fin n) (Fin n) S) = T := by
  have hM : cT s T * J * T = J := by
    ext a b
    have h := key (Pi.single a 1) (Pi.single b 1)
    rwa [hform_mulVec, hform_single_single_stabilizer_orbit_volume, hform_single_single_stabilizer_orbit_volume] at h
  have hdT : IsUnit T.det := by
    have h1 := congrArg Matrix.det hM
    rw [Matrix.det_mul, Matrix.det_mul] at h1
    have h2 : (cT s T).det = s T.det := by
      unfold cT
      rw [Matrix.det_transpose]
      exact (RingHom.map_det s T).symm
    rw [h2] at h1
    have h3 : s T.det * T.det * J.det = 1 * J.det := by linear_combination h1
    have h4 : s T.det * T.det = 1 := hdet.mul_left_inj.mp h3
    exact ⟨⟨T.det, s T.det, by rw [mul_comm]; exact h4, h4⟩, rfl⟩
  refine ⟨Matrix.nonsingInvUnit T hdT, ?_, rfl⟩
  show cT s T * J * T = J
  exact hM
end PI.VolStabSW.OrbR
