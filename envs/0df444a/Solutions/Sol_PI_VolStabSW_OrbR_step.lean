-- Prove2me | solution 1 for PI.VolStabSW.OrbR.step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:11:13.156648+00:00
-- url     : https://prove2.me/submissions/8b3eca97-e29d-47d8-968c-6f8022d67a4f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_HformEntry
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_OrbRing
import Theorems.Thm_PI_VolStabSW_OrbR_reflection_mulVec
import Theorems.Thm_PI_VolStabSW_OrbR_mem_UJ_of
import Theorems.Thm_PIW_AdelicOrbitU_hform_conj
import Theorems.Thm_PIW_AdelicOrbitU_hform_smul_left
import Theorems.Thm_PIW_AdelicOrbitU_hform_smul_right
import Theorems.Thm_PIW_AdelicOrbitU_hform_sub_left
import Theorems.Thm_PIW_AdelicOrbitU_hform_sub_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW PI.VolStabSW.OrbR
open Matrix Formalism.UG PIW.AdelicOrbitU
variable {S : Type} [CommRing S] (s : S →+* S) {n : ℕ} (J : Matrix (Fin n) (Fin n) S)
namespace PI.VolStabSW.OrbR
theorem _root_.solution (hs : ∀ z, s (s z) = z) (hJ : IsHerm s J) (hdet : IsUnit J.det)
    (a b : Fin n → S) (hab : hform s J b b = hform s J a a) (hu : IsUnit (hform s J a a))
    (lam : S) (hlam : lam * s lam = 1) (hc : IsUnit (hform s J a a - s lam * hform s J b a)) :
    ∃ g : GL (Fin n) S, g ∈ UJ s J ∧ (g : Matrix (Fin n) (Fin n) S) *ᵥ a = b ∧
      ∀ z, hform s J a z = 0 → hform s J b z = 0 → (g : Matrix (Fin n) (Fin n) S) *ᵥ z = z := by
  have hconj := hform_conj s J hs hJ
  obtain ⟨c, hc_def⟩ : ∃ c, hform s J a a - s lam * hform s J b a = c := ⟨_, rfl⟩
  rw [hc_def] at hc
  obtain ⟨ci, hci⟩ : ∃ ci, c * ci = 1 := hc.exists_right_inv
  have e2 : ci * c = 1 := by rw [mul_comm]; exact hci
  have e3 : s ci * s c = 1 := by rw [← map_mul, e2, map_one]
  obtain ⟨u, hu_def⟩ : ∃ u, a - lam • b = u := ⟨_, rfl⟩
  have hua : hform s J u a = c := by
    rw [← hu_def, hform_sub_left, hform_smul_left, hc_def]
  have huu : hform s J u u = c + s c := by
    rw [← hu_def, ← hc_def]
    simp only [hform_sub_left, hform_sub_right, hform_smul_left, hform_smul_right, map_sub, map_mul,
      hs, hconj]
    linear_combination (s lam * lam) * hab + hform s J a a * hlam
  have key1 : ∀ z w, hform s J (r1 s J ci u u *ᵥ z) (r1 s J ci u u *ᵥ w) = hform s J z w := by
    intro z w
    rw [reflection_mulVec, reflection_mulVec]
    simp only [hform_sub_left, hform_sub_right, hform_smul_left, hform_smul_right, map_mul, hconj, huu]
    linear_combination (hform s J z u * hform s J u w * s ci) * e2 +
      (hform s J z u * hform s J u w * ci) * e3
  obtain ⟨g1, hg1U, hg1⟩ := mem_UJ_of s J hdet _ key1
  obtain ⟨βi, hβ⟩ : ∃ βi, hform s J a a * βi = 1 := hu.exists_right_inv
  have hsβ : s (hform s J a a) = hform s J a a := hconj a a
  have hsβi : s βi = βi := by
    have h1 : hform s J a a * s βi = 1 := by rw [← hsβ, ← map_mul, hβ, map_one]
    calc s βi = s βi * (hform s J a a * βi) := by rw [hβ, mul_one]
      _ = (hform s J a a * s βi) * βi := by ring
      _ = βi := by rw [h1, one_mul]
  have key2 : ∀ z w, hform s J (r1 s J ((1 - s lam) * βi) b b *ᵥ z)
      (r1 s J ((1 - s lam) * βi) b b *ᵥ w) = hform s J z w := by
    intro z w
    rw [reflection_mulVec, reflection_mulVec]
    simp only [hform_sub_left, hform_sub_right, hform_smul_left, hform_smul_right, map_mul, hconj, hab,
      map_sub, map_one, hs, hsβi]
    linear_combination (hform s J z b * hform s J b w * βi) * hlam +
      (hform s J z b * hform s J b w * (1 - lam) * (1 - s lam) * βi) * hβ
  obtain ⟨g2, hg2U, hg2⟩ := mem_UJ_of s J hdet _ key2
  refine ⟨g2 * g1, mul_mem hg2U hg1U, ?_, ?_⟩
  · rw [Units.val_mul, ← mulVec_mulVec, hg1, hg2, reflection_mulVec s J ci u u, hua, e2, one_smul, ← hu_def,
      sub_sub_cancel, reflection_mulVec, hform_smul_right, hab, ← sub_smul]
    conv_rhs => rw [← one_smul S b]
    congr 1
    linear_combination hlam + (s lam * lam - lam) * hβ
  · intro z hz1 hz2
    have hzu : hform s J u z = 0 := by
      rw [← hu_def, hform_sub_left, hform_smul_left, hz1, hz2, mul_zero, sub_zero]
    rw [Units.val_mul, ← mulVec_mulVec, hg1, hg2, reflection_mulVec s J ci u u, hzu, mul_zero, zero_smul, sub_zero,
      reflection_mulVec, hz2, mul_zero, zero_smul, sub_zero]
end PI.VolStabSW.OrbR
