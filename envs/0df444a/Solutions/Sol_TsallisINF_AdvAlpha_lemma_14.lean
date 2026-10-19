-- Prove2me | solution 1 for TsallisINF.AdvAlpha.lemma_14
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-18T20:00:48.497374+00:00
-- url     : https://prove2.me/submissions/1f56e53a-95eb-4638-a511-da3850baf453

import Mathlib

set_option autoImplicit false

open Filter Topology

theorem solution (y : ℝ) (hy : 0 < y) :
    AntitoneOn (fun x : ℝ => (1 - y ^ (-x)) / x) (Set.Ioi 0) ∧
      Tendsto (fun x : ℝ => (1 - y ^ (-x)) / x) (𝓝[>] 0) (𝓝 (Real.log y)) ∧
      ∀ x : ℝ, 0 < x → (1 - y ^ (-x)) / x ≤ min x⁻¹ (Real.log y) := by
  have hrw : ∀ x : ℝ, y ^ (-x) = Real.exp (-(Real.log y * x)) := by
    intro x
    rw [Real.rpow_def_of_pos hy]; congr 1; ring
  set L := Real.log y with hL
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb hab
    simp only [Set.mem_Ioi] at ha hb
    simp only [hrw]
    have hc : Real.exp (-(L * a)) ≤ (1 - a / b) + a / b * Real.exp (-(L * b)) := by
      have h := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ (-(L * b)))
        (show (0:ℝ) ≤ 1 - a / b by rw [sub_nonneg, div_le_one hb]; exact hab)
        (show (0:ℝ) ≤ a / b by positivity) (by ring)
      have e : -(L * a) = (1 - a / b) • (0:ℝ) + (a / b) • (-(L * b)) := by
        simp only [smul_eq_mul]; field_simp; ring
      rw [e]
      simpa using h
    rw [div_le_div_iff₀ hb ha]
    have h3 := mul_le_mul_of_nonneg_right hc hb.le
    have h4 : a / b * Real.exp (-(L * b)) * b = a * Real.exp (-(L * b)) := by field_simp
    have h5 : (1 - a / b + a / b * Real.exp (-(L * b))) * b
        = b - a + a * Real.exp (-(L * b)) := by
      rw [add_mul, h4]; field_simp
    nlinarith
  · have hd : HasDerivAt (fun x : ℝ => 1 - Real.exp (-(L * x))) L 0 := by
      have h1 : HasDerivAt (fun x : ℝ => -(L * x)) (-(L * 1)) 0 :=
        ((hasDerivAt_id' (0:ℝ)).const_mul L).neg
      have h2 := (h1.exp).const_sub 1
      refine h2.congr_deriv ?_
      simp
    have := hd.tendsto_slope_zero_right
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [hrw, mul_zero, neg_zero, Real.exp_zero, sub_self, smul_eq_mul]
    simp [div_eq_inv_mul]
  · intro x hx
    rw [hrw]
    refine le_min ?_ ?_
    · have h : 1 - Real.exp (-(L * x)) ≤ 1 := by linarith [Real.exp_pos (-(L * x))]
      rw [inv_eq_one_div]
      exact div_le_div_of_nonneg_right h hx.le
    · rw [div_le_iff₀ hx]
      linarith [Real.add_one_le_exp (-(L * x))]
