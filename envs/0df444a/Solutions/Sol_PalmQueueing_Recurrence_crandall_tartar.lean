-- Prove2me | solution 1 for PalmQueueing.Recurrence.crandall_tartar
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T18:24:09.876788+00:00
-- url     : https://prove2.me/submissions/5c44cf07-27df-4ea7-b76a-60f453646214

import Mathlib
import Definitions.Def_PalmQueueing_Recurrence_MonotoneHomogeneous

/-!
# Theorem 2.11.1: the Crandall-Tartar theorem (§2.11.1, p.154)
-/


namespace PalmQueueing.Recurrence

theorem crandall_tartar_core {K : ℕ} (phi : (Fin K → ℝ) → Fin K → ℝ)
    (hhom : IsHomogeneousMap phi) :
    IsMonotoneMap phi ↔ IsNonExpansiveMap phi := by
  constructor
  · intro hmono x y
    set a : ℝ := ‖x - y‖ with ha
    have ha0 : 0 ≤ a := norm_nonneg _
    have hc : ∀ i, |x i - y i| ≤ a := by
      intro i
      have := norm_le_pi_norm (x - y) i
      simpa [Real.norm_eq_abs] using this
    have h1 : phi x ≤ phi y + a • onesVec K := by
      have hle : x ≤ y + a • onesVec K := by
        intro i
        simp only [Pi.add_apply, Pi.smul_apply, onesVec, smul_eq_mul, mul_one]
        have := hc i
        linarith [abs_le.mp this]
      have := hmono _ _ hle
      rw [hhom] at this
      intro i
      have h := this i
      simp only [Pi.add_apply] at h ⊢
      linarith
    have h2 : phi y ≤ phi x + a • onesVec K := by
      have hle : y ≤ x + a • onesVec K := by
        intro i
        simp only [Pi.add_apply, Pi.smul_apply, onesVec, smul_eq_mul, mul_one]
        have := hc i
        linarith [abs_le.mp this]
      have := hmono _ _ hle
      rw [hhom] at this
      intro i
      have h := this i
      simp only [Pi.add_apply] at h ⊢
      linarith
    rw [pi_norm_le_iff_of_nonneg ha0]
    intro i
    have e1 := h1 i
    have e2 := h2 i
    simp only [Pi.add_apply, Pi.smul_apply, onesVec, smul_eq_mul, mul_one] at e1 e2
    rw [Pi.sub_apply, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  · intro hne x y hxy
    set a : ℝ := ‖y - x‖ with ha
    have ha0 : 0 ≤ a := norm_nonneg _
    have hc : ∀ i, |y i - x i| ≤ a := by
      intro i
      have := norm_le_pi_norm (y - x) i
      simpa [Real.norm_eq_abs] using this
    have hz : ‖(x + a • onesVec K) - y‖ ≤ a := by
      rw [pi_norm_le_iff_of_nonneg ha0]
      intro i
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, onesVec, smul_eq_mul, mul_one]
      rw [Real.norm_eq_abs, abs_le]
      have h1 := hc i
      have h2 := hxy i
      constructor <;> linarith [abs_le.mp h1]
    have := hne (x + a • onesVec K) y
    rw [hhom] at this
    have hb := le_trans this hz
    intro i
    have := norm_le_pi_norm (a • onesVec K + phi x - phi y) i
    have hb' := le_trans this hb
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, onesVec, smul_eq_mul, mul_one,
      Real.norm_eq_abs] at hb'
    linarith [abs_le.mp hb']

end PalmQueueing.Recurrence

open PalmQueueing.Recurrence


theorem solution {K : ℕ} (phi : (Fin K → ℝ) → Fin K → ℝ)
    (hhom : IsHomogeneousMap phi) :
    IsMonotoneMap phi ↔ IsNonExpansiveMap phi := by
  exact crandall_tartar_core phi hhom
