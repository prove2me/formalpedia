-- Prove2me | solution 1 for QGradGAW.Smooth.lemma_22_coeff_sum
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T17:24:54.680675+00:00
-- url     : https://prove2.me/submissions/116da065-b7d3-4a7b-ad81-0e9b72105efa

import Mathlib
import Definitions.Def_QGradGAW_Smooth_Setting

set_option autoImplicit false
open QGradGAW.Smooth

lemma qg_choose_lt (m l : ℕ) (hm : 1 ≤ m) (hl : 1 ≤ l) : m.choose l < (m + l).choose l := by
  obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
  have h1 : (m + (l' + 1)).choose (l' + 1) = (m + l').choose l' + (m + l').choose (l' + 1) := by
    rw [show m + (l' + 1) = (m + l') + 1 by ring, Nat.choose_succ_succ]
  have h2 : m.choose (l' + 1) ≤ (m + l').choose (l' + 1) :=
    Nat.choose_le_choose _ (by omega)
  have h3 : 0 < (m + l').choose l' := Nat.choose_pos (by omega)
  omega

lemma qg_abs_cc (m l : ℕ) (hl : 1 ≤ l) (hlm : l ≤ m) :
    |centralCoeff m (l : ℤ)| = (1 / (l : ℝ)) * ((m.choose l : ℝ) / ((m + l).choose l : ℝ)) := by
  have hl0 : (l : ℤ) ≠ 0 := by omega
  simp only [centralCoeff, if_neg hl0, Int.natAbs_natCast]
  have hpos : (0:ℝ) < ((m + l).choose l : ℝ) := by
    have : 0 < (m + l).choose l := Nat.choose_pos (by omega)
    exact_mod_cast this
  have hlr : (0:ℝ) < (l:ℝ) := by exact_mod_cast hl
  push_cast
  have e1 : |(-1:ℝ) ^ ((l:ℤ) - 1) / (l:ℝ)| = 1 / (l:ℝ) := by
    rw [abs_div, abs_zpow]; simp [abs_of_pos hlr]
  have e2 : |(m.choose l : ℝ) / ((m + l).choose l : ℝ)| = (m.choose l : ℝ) / ((m + l).choose l : ℝ) :=
    abs_of_nonneg (by positivity)
  rw [abs_mul, e1, e2]

lemma qg_abs_cc_lt (m l : ℕ) (hm : 1 ≤ m) (hl : 1 ≤ l) (hlm : l ≤ m) :
    |centralCoeff m (l : ℤ)| < 1 / (l : ℝ) := by
  rw [qg_abs_cc m l hl hlm]
  have hpos : (0:ℝ) < ((m + l).choose l : ℝ) := by
    have : 0 < (m + l).choose l := Nat.choose_pos (by omega)
    exact_mod_cast this
  have hlr : (0:ℝ) < (l:ℝ) := by exact_mod_cast hl
  have h : ((m.choose l : ℕ) : ℝ) < (((m + l).choose l : ℕ) : ℝ) := by
    exact_mod_cast qg_choose_lt m l hm hl
  have h2 : ((m.choose l : ℝ) / ((m + l).choose l : ℝ)) < 1 := by
    rw [div_lt_one hpos]; exact h
  have : 0 < 1 / (l : ℝ) := by positivity
  nlinarith

lemma qg_cc_zero (m : ℕ) : centralCoeff m 0 = 0 := by simp [centralCoeff]

lemma qg_harm (m : ℕ) : ∑ ℓ ∈ Finset.Icc 1 m, (1 : ℝ) / ℓ ≤ Real.log m + 1 := by
  have h := harmonic_le_one_add_log m
  rw [harmonic_eq_sum_Icc] at h
  have h' : ((∑ i ∈ Finset.Icc 1 m, ((i : ℚ))⁻¹ : ℚ) : ℝ) ≤ 1 + Real.log m := by exact_mod_cast h
  push_cast at h'
  simp only [one_div]
  linarith

lemma qg_sum_lt (m : ℕ) (hm : 1 ≤ m) :
    ∑ ℓ ∈ Finset.range (m + 1), |centralCoeff m (ℓ : ℤ)| < ∑ ℓ ∈ Finset.Icc 1 m, (1 : ℝ) / ℓ := by
  have hI : Finset.Icc 1 m = Finset.Ico 1 (m+1) := by ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), hI]
  simp only [Nat.cast_zero, qg_cc_zero, abs_zero, zero_add]
  apply Finset.sum_lt_sum_of_nonempty
  · exact ⟨1, by simp only [Finset.mem_Ico]; omega⟩
  · intro l hl
    simp only [Finset.mem_Ico] at hl
    exact qg_abs_cc_lt m l hm hl.1 (by omega)

theorem solution (m : ℕ) (hm : 1 ≤ m) :
    ∑ ℓ ∈ Finset.range (m + 1), |centralCoeff m (ℓ : ℤ)| < ∑ ℓ ∈ Finset.Icc 1 m, (1 : ℝ) / ℓ ∧
      ∑ ℓ ∈ Finset.Icc 1 m, (1 : ℝ) / ℓ ≤ Real.log m + 1 :=
  ⟨qg_sum_lt m hm, qg_harm m⟩
