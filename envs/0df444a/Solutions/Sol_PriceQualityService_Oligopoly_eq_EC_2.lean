-- Prove2me | solution 1 for PriceQualityService.Oligopoly.eq_EC_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T09:26:01.001831+00:00
-- url     : https://prove2.me/submissions/b469f55e-08a1-4647-933e-2c3a1cec3f05

import Mathlib
set_option autoImplicit false

lemma ec2_aux_mono (u v : ℝ) (huv : u < v) (hv : v ≤ 1) :
    u * Real.exp (-u) < v * Real.exp (-v) := by
  set d := v - u with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  have h1 : (1 - d) < Real.exp (-d) := by
    have := Real.add_one_lt_exp (x := -d) (by linarith)
    linarith
  have h2 : (1 - d) * Real.exp d < 1 := by
    have := mul_lt_mul_of_pos_right h1 (Real.exp_pos d)
    rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at this
  have h3 : 0 < Real.exp d - 1 := by
    have := Real.add_one_lt_exp (x := d) hd0.ne'
    linarith
  have h4 : u * (Real.exp d - 1) < d := by
    have : u * (Real.exp d - 1) ≤ (1 - d) * (Real.exp d - 1) :=
      mul_le_mul_of_nonneg_right (by rw [hd]; linarith) h3.le
    nlinarith
  have hv' : v = u + d := by rw [hd]; ring
  have e1 : Real.exp (-u) = Real.exp (-v) * Real.exp d := by
    rw [← Real.exp_add]; congr 1; rw [hd]; ring
  rw [e1]
  have := Real.exp_pos (-v)
  nlinarith [mul_pos this h3]

lemma ec2_aux_anti (u v : ℝ) (huv : u < v) (hu : 1 ≤ u) :
    v * Real.exp (-v) < u * Real.exp (-u) := by
  set d := v - u with hd
  have hd0 : 0 < d := by rw [hd]; linarith
  have h3 : d < Real.exp d - 1 := by
    have := Real.add_one_lt_exp (x := d) hd0.ne'
    linarith
  have h4 : d < u * (Real.exp d - 1) := by
    nlinarith
  have hv' : v = u + d := by rw [hd]; ring
  have e1 : Real.exp (-u) = Real.exp (-v) * Real.exp d := by
    rw [← Real.exp_add]; congr 1; rw [hd]; ring
  rw [e1]
  have := Real.exp_pos (-v)
  nlinarith [mul_pos this (sub_pos.mpr h4)]

theorem solution (α a b c s q t r : ℝ) :
    StrictMonoOn
        (fun p : ℝ => (p - c * q ^ 2 - t * (a - b * q) - r) * Real.exp (α * q - p + t * s))
        (Set.Iic (c * q ^ 2 + t * (a - b * q) + r + 1)) ∧
      StrictAntiOn
        (fun p : ℝ => (p - c * q ^ 2 - t * (a - b * q) - r) * Real.exp (α * q - p + t * s))
        (Set.Ici (c * q ^ 2 + t * (a - b * q) + r + 1)) ∧
      ((c * q ^ 2 + t * (a - b * q) + r + 1) - c * q ^ 2 - t * (a - b * q) - r) *
          Real.exp (α * q - (c * q ^ 2 + t * (a - b * q) + r + 1) + t * s) =
        Real.exp (α * q - c * q ^ 2 - t * (a - b * q - s) - r - 1) := by
  set K := c * q ^ 2 + t * (a - b * q) + r with hK
  have key : ∀ p : ℝ, (p - c * q ^ 2 - t * (a - b * q) - r) * Real.exp (α * q - p + t * s)
      = Real.exp (α * q + t * s - K) * ((p - K) * Real.exp (-(p - K))) := by
    intro p
    have : Real.exp (α * q - p + t * s) = Real.exp (α * q + t * s - K) * Real.exp (-(p - K)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this, hK]; ring
  have hC := Real.exp_pos (α * q + t * s - K)
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [key]
    exact mul_lt_mul_of_pos_left (ec2_aux_mono _ _ (by linarith) (by simp only [Set.mem_Iic] at hy; linarith)) hC
  · intro x hx y hy hxy
    simp only [key]
    exact mul_lt_mul_of_pos_left (ec2_aux_anti _ _ (by linarith) (by simp only [Set.mem_Ici] at hx; linarith)) hC
  · have : α * q - (K + 1) + t * s = α * q - c * q ^ 2 - t * (a - b * q - s) - r - 1 := by
      rw [hK]; ring
    simp only [hK] at this ⊢
    rw [← this]; ring_nf
