-- Prove2me | solution 1 for TitiusBode.resonance_two_three
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-10-10T19:32:34.683975+00:00
-- url     : https://prove2.me/submissions/a5b9b9a1-4b09-4346-880c-a0023a82ae56

import Definitions.Def_TitiusBode_Defs
import Mathlib
open Filter Topology
open TitiusBode

theorem solution (K T₁ T₂ : ℝ) (hK : 0 < K) (hT₁ : 0 < T₁)
    (hres : T₁ / T₂ = 2 / 3) :
    |100 * deviation (K * T₁ ^ ((2 : ℝ) / 3)) (K * T₂ ^ ((2 : ℝ) / 3)) - (-23.69)| < 0.005 ∧
    |100 * deviation (K * T₂ ^ ((2 : ℝ) / 3)) (K * T₁ ^ ((2 : ℝ) / 3)) - 31.04| < 0.005 := by
  have hT₂ne : T₂ ≠ 0 := by
    rintro rfl; norm_num at hres
  have hT₁eq : T₁ = 2 / 3 * T₂ := by
    field_simp at hres; linarith
  have hT₂ : 0 < T₂ := by linarith
  set x : ℝ := ((2 : ℝ) / 3) ^ ((2 : ℝ) / 3) with hx
  set y : ℝ := ((3 : ℝ) / 2) ^ ((2 : ℝ) / 3) with hy
  set u : ℝ := T₂ ^ ((2 : ℝ) / 3) with hu
  have hu0 : 0 < u := Real.rpow_pos_of_pos hT₂ _
  have hx0 : 0 < x := Real.rpow_pos_of_pos (by norm_num) _
  have hy0 : 0 < y := Real.rpow_pos_of_pos (by norm_num) _
  -- cube of a `2/3`-power
  have hcube : ∀ a : ℝ, 0 ≤ a → (a ^ ((2 : ℝ) / 3)) ^ 3 = a ^ 2 := by
    intro a ha
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha]
    norm_num
  have hx3 : x ^ 3 = 4 / 9 := by rw [hx, hcube _ (by norm_num)]; norm_num
  have hy3 : y ^ 3 = 9 / 4 := by rw [hy, hcube _ (by norm_num)]; norm_num
  have hxy : x * y = 1 := by
    rw [hx, hy, ← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
  have hT₁pow : T₁ ^ ((2 : ℝ) / 3) = x * u := by
    rw [hT₁eq, Real.mul_rpow (by norm_num) hT₂.le]
  -- certified bounds
  have hxlo : 0.76305 < x := by
    by_contra h; push_neg at h
    have : x ^ 3 ≤ 0.76305 ^ 3 := pow_le_pow_left₀ hx0.le h 3
    rw [hx3] at this; norm_num at this
  have hxhi : x < 0.76315 := by
    by_contra h; push_neg at h
    have : 0.76315 ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) h 3
    rw [hx3] at this; norm_num at this
  have hylo : 1.31035 < y := by
    by_contra h; push_neg at h
    have : y ^ 3 ≤ 1.31035 ^ 3 := pow_le_pow_left₀ hy0.le h 3
    rw [hy3] at this; norm_num at this
  have hyhi : y < 1.31045 := by
    by_contra h; push_neg at h
    have : 1.31045 ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ (by norm_num) h 3
    rw [hy3] at this; norm_num at this
  have hd1 : deviation (K * T₁ ^ ((2 : ℝ) / 3)) (K * u) = x - 1 := by
    unfold deviation; rw [hT₁pow]; field_simp
  have hd2 : deviation (K * u) (K * T₁ ^ ((2 : ℝ) / 3)) = y - 1 := by
    unfold deviation; rw [hT₁pow]
    have : y = 1 / x := by field_simp; linarith
    rw [this]; field_simp
  rw [hd1, hd2]
  constructor
  · rw [abs_lt]; constructor <;> linarith
  · rw [abs_lt]; constructor <;> linarith
