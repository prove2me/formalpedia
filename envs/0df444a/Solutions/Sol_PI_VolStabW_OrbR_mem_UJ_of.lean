-- Prove2me | solution 1 for PI.VolStabW.OrbR.mem_UJ_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:36:13.436966+00:00
-- url     : https://prove2.me/submissions/69cf9a50-0ca5-4e36-b98c-3f53ada9ed10

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_HformEntry
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_OrbRing
import Theorems.Thm_PIW_AdelicOrbitU_hform_entry
import Theorems.Thm_PIW_AdelicOrbitU_hform_single


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
theorem _root_.solution (hdet : IsUnit J.det) (T : Matrix (Fin n) (Fin n) S)
    (key : ∀ z w, hform s J (T *ᵥ z) (T *ᵥ w) = hform s J z w) :
    ∃ g : GL (Fin n) S, g ∈ UJ s J ∧ (g : Matrix (Fin n) (Fin n) S) = T := by
  have hM : cT s T * J * T = J := by
    ext i j
    rw [hform_entry, key, hform_single]
  have hL : (J⁻¹ * cT s T * J) * T = 1 := by
    calc (J⁻¹ * cT s T * J) * T = J⁻¹ * (cT s T * J * T) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hM, nonsing_inv_mul _ hdet]
  have hR : T * (J⁻¹ * cT s T * J) = 1 := mul_eq_one_comm.mp hL
  exact ⟨⟨T, J⁻¹ * cT s T * J, hR, hL⟩, hM, rfl⟩
end PI.VolStabW.OrbR
