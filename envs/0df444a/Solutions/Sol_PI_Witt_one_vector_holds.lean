-- Prove2me | solution 1 for PI.Witt.one_vector_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:31:08.394194+00:00
-- url     : https://prove2.me/submissions/73bdbf1a-dff6-4bf5-aaa9-62b18b3aeccd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_Anisotropic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_OneVector
import Theorems.Thm_PI_Witt_qrefl_isometry
import Theorems.Thm_PI_Witt_oneVector_generic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Witt
namespace PI.Witt
theorem _root_.solution : OneVector := by
  intro K V _ _ _ _ _ B hB x y hxy hx0
  by_cases ha : B (x - y) x ≠ 0
  · exact oneVector_generic B hB x y hxy ha
  · push_neg at ha
    have hyx : B y x = B x x := by
      have h : B (x - y) x = B x x - B y x := by simp only [map_sub, LinearMap.sub_apply]
      rw [h] at ha
      exact (sub_eq_zero.1 ha).symm
    have hxy' : B x x = B (-y) (-y) := by simp [hxy]
    have ha2 : B (x - -y) x ≠ 0 := by
      rw [sub_neg_eq_add, map_add, LinearMap.add_apply, hyx]
      intro h
      apply hx0
      have h2 : (2 : K) * B x x = 0 := by rw [two_mul]; exact h
      exact (mul_eq_zero.1 h2).resolve_left two_ne_zero
    obtain ⟨g1, hg1, hg1x, hg1z⟩ := oneVector_generic B hB x (-y) hxy' ha2
    have hyy : B y y ≠ 0 := hxy ▸ hx0
    have ha0 : B y y / 2 ≠ 0 := div_ne_zero hyy two_ne_zero
    have hstar : star (B y y / 2) = B y y / 2 := by rw [star_div₀, hB, star_ofNat]
    have hv : B y y = B y y / 2 + star (B y y / 2) := by rw [hstar]; ring
    have h2 : (B y y / 2)⁻¹ * B y y = 2 := by field_simp
    refine ⟨g1.trans (qreflEquiv B y (B y y / 2) ha0 hv), fun z w => ?_, ?_, fun z hz1 hz2 => ?_⟩
    · simp only [LinearEquiv.trans_apply]
      have hq : ∀ u, qreflEquiv B y (B y y / 2) ha0 hv u = qrefl B y (B y y / 2) u := fun _ => rfl
      rw [hq, hq, qrefl_isometry B hB y _ ha0 hv, hg1]
    · simp only [LinearEquiv.trans_apply, hg1x]
      show qrefl B y (B y y / 2) (-y) = y
      rw [qrefl_apply, map_neg, mul_neg, neg_smul, sub_neg_eq_add, h2, two_smul]
      abel
    · simp only [LinearEquiv.trans_apply]
      rw [hg1z z hz1 (by rw [map_neg, LinearMap.neg_apply, hz2, neg_zero])]
      show qrefl B y (B y y / 2) z = z
      rw [qrefl_apply, hz2, mul_zero, zero_smul, sub_zero]
end PI.Witt
