-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.isK_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:55:26.891928+00:00
-- url     : https://prove2.me/submissions/9a39ba78-13d1-4cc9-b0b8-4f1aa97a7419

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_SelfDualStd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_IsKTheta
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_isK_int
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_smulHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.UnitaryGroupMassFormula.UnimodLocStd.smulHom_apply



set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable (b : ℤ) (d : ℕ)
variable {b d}
variable {e : ℤ} (hn : cmTheta b d * (b - cmTheta b d) = (e : ℂ))
include hn
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution {t : ℂ} (h : IsK b d t) : IsK b d t⁻¹ := by
  by_cases ht : t = 0
  · rw [ht, inv_zero]
    simpa using PI.UnitaryGroupMassFormula.UnimodLocStd.isK_int (b := b) (d := d) 0
  obtain ⟨p, q, r, hr, h⟩ := h
  have hrt : (r : ℂ) * t ≠ 0 := mul_ne_zero (Int.cast_ne_zero.mpr hr) ht

  have hz : ((p ^ 2 + p * q * b + q ^ 2 * e : ℤ) : ℂ) =
      (r : ℂ) * t * (p + q * b - q * cmTheta b d) := by
    rw [h]
    push_cast
    linear_combination (-(q : ℂ) ^ 2) * hn
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  by_cases hN : p ^ 2 + p * q * b + q ^ 2 * e = 0
  ·
    have hw : (p : ℂ) + q * b - q * cmTheta b d = 0 := by
      have h0 : (r : ℂ) * t * (p + q * b - q * cmTheta b d) = 0 := by
        rw [← hz, hN, Int.cast_zero]
      exact (mul_eq_zero.mp h0).resolve_left hrt
    have hk : (r : ℂ) * t = ((2 * p + q * b : ℤ) : ℂ) := by
      rw [h]
      push_cast
      linear_combination -hw
    have hk0 : (2 * p + q * b : ℤ) ≠ 0 := by
      intro h0
      rw [h0, Int.cast_zero] at hk
      exact hrt hk
    refine ⟨r, 0, 2 * p + q * b, hk0, ?_⟩
    rw [← hk, mul_inv_cancel_right₀ ht]
    simp
  · refine ⟨r * (p + q * b), -(r * q), p ^ 2 + p * q * b + q ^ 2 * e, hN, ?_⟩
    rw [hz]
    field_simp
    push_cast
    ring
end PI.UnitaryGroupMassFormula.UnimodLocStd
