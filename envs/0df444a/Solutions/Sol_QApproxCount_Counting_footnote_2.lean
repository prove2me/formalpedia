-- Prove2me | solution 1 for QApproxCount.Counting.footnote_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:32:42.530618+00:00
-- url     : https://prove2.me/submissions/2532d9fe-025d-4873-a484-37c258488a5d

import Mathlib
set_option autoImplicit false

theorem solution (θ ε : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 0.002) (hε : 0 < ε) (hε1 : ε < 1) :
    1 - ε ≤ Real.sin (θ * (1 + ε / 5)) ^ 2 / Real.sin θ ^ 2 ∧
      Real.sin (θ * (1 + ε / 5)) ^ 2 / Real.sin θ ^ 2 ≤ 1 + ε := by
  have hθ1' : θ ≤ 1 := by linarith
  have hsθ : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ (by linarith [Real.pi_gt_three])
  set r : ℝ := 1 + ε / 5 with hr
  have hr1 : 1 ≤ r := by rw [hr]; linarith
  have hr2 : r ≤ 1.2 := by rw [hr]; linarith
  have hrθ : 0 < r * θ := by positivity
  have hrθ' : r * θ ≤ 0.0024 := by nlinarith
  have hpi : (0.0024 : ℝ) < Real.pi := by linarith [Real.pi_gt_three]
  have hs2 : 0 < Real.sin (θ * r) := by
    apply Real.sin_pos_of_pos_of_lt_pi (by nlinarith) (by nlinarith)
  -- monotonicity: sin θ ≤ sin (θ r)
  have hmono : Real.sin θ ≤ Real.sin (θ * r) := by
    apply Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three]) (by nlinarith)
  -- concavity: sin (θ r) ≤ r sin θ
  have hconc : Real.sin (θ * r) ≤ r * Real.sin θ := by
    have hc := strictConcaveOn_sin_Icc.concaveOn
    have h0 : (0:ℝ) ∈ Set.Icc 0 Real.pi := ⟨le_refl _, Real.pi_pos.le⟩
    have h1 : θ * r ∈ Set.Icc 0 Real.pi := ⟨by nlinarith, by nlinarith⟩
    have ha : (0:ℝ) ≤ 1 - 1/r := by
      rw [sub_nonneg, div_le_one (by linarith)]; exact hr1
    have hb : (0:ℝ) ≤ 1/r := by positivity
    have key := hc.2 h0 h1 ha hb (by ring)
    simp only [smul_eq_mul, mul_zero, zero_add, Real.sin_zero] at key
    have e : 1 / r * (θ * r) = θ := by field_simp
    rw [e] at key
    have : Real.sin (θ * r) ≤ r * Real.sin θ := by
      have := mul_le_mul_of_nonneg_left key (by linarith : (0:ℝ) ≤ r)
      calc Real.sin (θ * r) = r * (1 / r * Real.sin (θ * r)) := by field_simp
        _ ≤ r * Real.sin θ := by nlinarith
    exact this
  have hpos : 0 < Real.sin θ ^ 2 := by positivity
  constructor
  · rw [le_div_iff₀ hpos]
    have : Real.sin θ ^ 2 ≤ Real.sin (θ * r) ^ 2 := by nlinarith
    nlinarith [sq_nonneg (Real.sin θ)]
  · rw [div_le_iff₀ hpos]
    have h : Real.sin (θ * r) ^ 2 ≤ (r * Real.sin θ) ^ 2 := by nlinarith
    have : r ^ 2 ≤ 1 + ε := by rw [hr]; nlinarith
    nlinarith [sq_nonneg (Real.sin θ)]
