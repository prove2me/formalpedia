-- Prove2me | solution 1 for RobustSPA.Affiliated.pointwise_bound_aff
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:00:48.503013+00:00
-- url     : https://prove2.me/submissions/7de042c3-5232-483f-9c69-f883f5160cd9

import Mathlib

set_option autoImplicit false

theorem solution (n : ℕ) (hn : 2 ≤ n) (r : ℝ) (hr : 0 < r) (p : ℝ) (hp : p ∈ Set.Ioo r 1) :
    let g : ℝ → ℝ := fun z => ((n : ℝ) - 1) * r / (p - r) - 1 - ((n : ℝ) - 1) * p / (p - r) * z +
      (n : ℝ) * z ^ (((n : ℝ) - 1) / (n : ℝ))
    IsGreatest (g '' Set.Icc 0 1) (g ((1 - r / p) ^ n)) ∧
      g ((1 - r / p) ^ n) = ((n : ℝ) - 1) * r / (p - r) - 1 - ((n : ℝ) - 1) * p / (p - r) * (1 - r / p) ^ n +
        (n : ℝ) * (1 - r / p) ^ (n - 1) := by
  intro g
  obtain ⟨hrp, hp1⟩ := hp
  have hp0 : 0 < p := hr.trans hrp
  set q : ℝ := 1 - r / p with hq
  have hq0 : 0 < q := by
    have : r / p < 1 := (div_lt_one hp0).2 hrp
    rw [hq]; linarith
  have hq1 : q < 1 := by
    have : 0 < r / p := div_pos hr hp0
    rw [hq]; linarith
  have hpr : 0 < p - r := sub_pos.2 hrp
  have hqeq : q = (p - r) / p := by rw [hq]; field_simp
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hcoef : ((n : ℝ) - 1) * p / (p - r) = ((n : ℝ) - 1) / q := by
    rw [hqeq]; field_simp
  have hqn : q ^ n = q ^ (n - 1) * q := by
    rw [← pow_succ]; congr 1; omega
  have hQm : 0 < q ^ (n - 1) := pow_pos hq0 _
  have hrpow : (q ^ n) ^ (((n : ℝ) - 1) / n) = q ^ (n - 1) := by
    rw [← Real.rpow_natCast q n, ← Real.rpow_mul hq0.le]
    have : (n : ℝ) * (((n : ℝ) - 1) / n) = ((n - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub (by omega : 1 ≤ n)]; push_cast; field_simp
    rw [this, Real.rpow_natCast]
  have key : ∀ z : ℝ, 0 ≤ z → (n : ℝ) * z ^ (((n : ℝ) - 1) / n) ≤ ((n : ℝ) - 1) / q * z + q ^ (n - 1) := by
    intro z hz
    have hqnpos : 0 < q ^ n := pow_pos hq0 _
    have am := Real.geom_mean_le_arith_mean2_weighted (w₁ := ((n : ℝ) - 1) / n) (w₂ := 1 / n)
      (p₁ := z / q ^ n) (p₂ := 1) (by apply div_nonneg <;> linarith) (by positivity)
      (by positivity) (by norm_num) (by field_simp; ring)
    rw [Real.one_rpow, mul_one, Real.div_rpow hz hqnpos.le, hrpow] at am
    have e : (n : ℝ) * z ^ (((n : ℝ) - 1) / n) = n * q ^ (n - 1) * (z ^ (((n : ℝ) - 1) / n) / q ^ (n - 1)) := by
      field_simp
    have e2 : ((n : ℝ) - 1) / q * z + q ^ (n - 1) =
        n * q ^ (n - 1) * (((n : ℝ) - 1) / n * (z / q ^ n) + 1 / n * 1) := by
      rw [hqn]; field_simp
    rw [e, e2]
    exact mul_le_mul_of_nonneg_left am (by positivity)
  have hgq : g (q ^ n) = ((n : ℝ) - 1) * r / (p - r) - 1 - ((n : ℝ) - 1) * p / (p - r) * q ^ n +
        (n : ℝ) * q ^ (n - 1) := by
    show ((n : ℝ) - 1) * r / (p - r) - 1 - ((n : ℝ) - 1) * p / (p - r) * q ^ n +
      (n : ℝ) * (q ^ n) ^ (((n : ℝ) - 1) / n) = _
    rw [hrpow]
  refine ⟨⟨⟨q ^ n, ⟨(pow_pos hq0 _).le, pow_le_one₀ hq0.le hq1.le⟩, rfl⟩, ?_⟩, hgq⟩
  rintro _ ⟨z, hz, rfl⟩
  have hk := key z hz.1
  have hc : ((n : ℝ) - 1) * p / (p - r) * q ^ n = ((n : ℝ) - 1) * q ^ (n - 1) := by
    rw [hcoef, hqn]; field_simp
  rw [hgq, hc]
  show ((n : ℝ) - 1) * r / (p - r) - 1 - ((n : ℝ) - 1) * p / (p - r) * z +
      (n : ℝ) * z ^ (((n : ℝ) - 1) / (n : ℝ)) ≤ _
  rw [hcoef] at *
  linarith
