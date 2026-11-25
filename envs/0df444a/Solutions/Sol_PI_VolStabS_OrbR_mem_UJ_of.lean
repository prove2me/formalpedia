-- Prove2me | solution 1 for PI.VolStabS.OrbR.mem_UJ_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:51:02.889322+00:00
-- url     : https://prove2.me/submissions/f706a246-369c-41ab-833b-71f61578c183

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_HformEntry
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_OrbRing
import Theorems.Thm_PI_VolStabS_OrbR_hform_mulVec

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS PI.VolStabS.OrbR
open Matrix Formalism.UG PIW.AdelicOrbitU
variable {S : Type} [CommRing S] (s : S →+* S) {n : ℕ} (J : Matrix (Fin n) (Fin n) S)
namespace PI.VolStabS.OrbR
theorem _root_.solution (hdet : IsUnit J.det) (T : Matrix (Fin n) (Fin n) S)
    (key : ∀ z w, hform s J (T *ᵥ z) (T *ᵥ w) = hform s J z w) :
    ∃ g : GL (Fin n) S, g ∈ UJ s J ∧ (g : Matrix (Fin n) (Fin n) S) = T := by
  have hsingle : ∀ (M : Matrix (Fin n) (Fin n) S) (i j : Fin n),
      hform s M (Pi.single i 1) (Pi.single j 1) = M i j := by
    intro M i j
    simp [hform, Pi.single_apply, apply_ite s]
  have hM : cT s T * J * T = J := by
    ext i j
    have h1 := key (Pi.single i 1) (Pi.single j 1)
    rwa [hform_mulVec, hsingle, hsingle] at h1
  have h2 := congrArg Matrix.det hM
  rw [Matrix.det_mul, Matrix.det_mul] at h2
  have h3 : (cT s T).det * T.det = 1 :=
    hdet.mul_left_cancel (by linear_combination h2)
  have hT : IsUnit T := (Matrix.isUnit_iff_isUnit_det T).2 (IsUnit.of_mul_eq_one_right _ h3)
  refine ⟨hT.unit, ?_, hT.unit_spec⟩
  show cT s (hT.unit : Matrix (Fin n) (Fin n) S) * J * (hT.unit : Matrix (Fin n) (Fin n) S) = J
  rw [hT.unit_spec]
  exact hM
end PI.VolStabS.OrbR
