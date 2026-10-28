-- Prove2me | solution 1 for UniformDRO.LowerBound.taylor_display
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:40:28.066135+00:00
-- url     : https://prove2.me/submissions/e4f9a952-ba60-483d-a488-8fe912e0b53e

import Mathlib
import Definitions.Def_UniformDRO_LowerBound_Setting

open UniformDRO.LowerBound in
theorem solution (k ρ : ℝ) (hk : 1 < k) (hρ : 0 < ρ) (δ : ℝ) (hδ : 0 < δ)
    (hδp : δ ≤ pk k ρ) :
    UniformDRO.Concentration.ck k ρ * (pk k ρ - δ) ^ (1 / UniformDRO.Concentration.kstar k) ≤
        UniformDRO.Concentration.ck k ρ * (UniformDRO.Concentration.ck k ρ ^ (-1 : ℝ) - 1 / UniformDRO.Concentration.kstar k * UniformDRO.Concentration.ck k ρ ^ (UniformDRO.Concentration.kstar k / k) * δ) ∧
      UniformDRO.Concentration.ck k ρ * (UniformDRO.Concentration.ck k ρ ^ (-1 : ℝ) - 1 / UniformDRO.Concentration.kstar k * UniformDRO.Concentration.ck k ρ ^ (UniformDRO.Concentration.kstar k / k) * δ) =
        1 - 1 / UniformDRO.Concentration.kstar k * UniformDRO.Concentration.ck k ρ ^ UniformDRO.Concentration.kstar k * δ := by
  have hk0 : 0 < k := by linarith
  have hk1 : 0 < k - 1 := by linarith
  set B := 1 + k * (k - 1) * ρ with hBdef
  have hB : 1 < B := by
    have : 0 < k * (k - 1) * ρ := by positivity
    linarith
  have hB0 : 0 < B := by linarith
  have hc : UniformDRO.Concentration.ck k ρ = B ^ (1 / k) := rfl
  have ha : pk k ρ = B ^ (-(1 / (k - 1))) := rfl
  have hks : UniformDRO.Concentration.kstar k = k / (k - 1) := rfl
  have hr : 1 / UniformDRO.Concentration.kstar k = (k - 1) / k := by rw [hks]; field_simp
  set c := UniformDRO.Concentration.ck k ρ with hcdef
  set a := pk k ρ with hadef
  have hc0 : 0 < c := by rw [hc]; exact Real.rpow_pos_of_pos hB0 _
  have ha0 : 0 < a := by rw [ha]; exact Real.rpow_pos_of_pos hB0 _
  have cpow : ∀ x : ℝ, c ^ x = B ^ (1 / k * x) := fun x => by
    rw [hc, ← Real.rpow_mul hB0.le]
  have apow : ∀ x : ℝ, a ^ x = B ^ (-(1 / (k - 1)) * x) := fun x => by
    rw [ha, ← Real.rpow_mul hB0.le]
  set r := 1 / UniformDRO.Concentration.kstar k with hrdef
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r ≤ 1 := by rw [hr, div_le_one hk0]; linarith
  -- a^r = c^(-1), a^(r-1) = c^(kstar/k)
  have h1 : a ^ r = c ^ (-1 : ℝ) := by
    rw [apow, cpow, hr]
    congr 1
    field_simp
  have h2 : a ^ (r - 1) = c ^ (UniformDRO.Concentration.kstar k / k) := by
    rw [apow, cpow, hr, hks]
    congr 1
    field_simp
    ring
  constructor
  · apply mul_le_mul_of_nonneg_left _ hc0.le
    have hs : -1 ≤ -δ / a := by
      rw [neg_div, neg_le_neg_iff, div_le_one ha0]; exact hδp
    have hbern := rpow_one_add_le_one_add_mul_self hs hr0 hr1
    have hfac : a - δ = a * (1 + -δ / a) := by field_simp; ring
    rw [hfac, Real.mul_rpow ha0.le (by linarith [hs]), ← h1, ← h2]
    have hsub : a ^ (r - 1) = a ^ r / a := Real.rpow_sub_one ha0.ne' r
    rw [hsub]
    have hpos : 0 < a ^ r := Real.rpow_pos_of_pos ha0 r
    calc a ^ r * (1 + -δ / a) ^ r ≤ a ^ r * (1 + r * (-δ / a)) :=
          mul_le_mul_of_nonneg_left hbern hpos.le
      _ = a ^ r - r * (a ^ r / a) * δ := by field_simp; ring
  · have e1 : c * c ^ (-1 : ℝ) = 1 := by
      rw [Real.rpow_neg_one, mul_inv_cancel₀ hc0.ne']
    have e2 : c * c ^ (UniformDRO.Concentration.kstar k / k) = c ^ UniformDRO.Concentration.kstar k := by
      have hx : UniformDRO.Concentration.kstar k = 1 + UniformDRO.Concentration.kstar k / k := by
        rw [hks]
        field_simp
        ring
      conv_rhs => rw [hx]
      rw [Real.rpow_add hc0, Real.rpow_one]
    rw [mul_sub, e1]
    rw [show c * (r * c ^ (UniformDRO.Concentration.kstar k / k) * δ) =
      r * (c * c ^ (UniformDRO.Concentration.kstar k / k)) * δ by ring, e2]
