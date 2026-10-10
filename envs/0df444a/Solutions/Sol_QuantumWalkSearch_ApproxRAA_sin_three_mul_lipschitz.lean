-- Prove2me | solution 1 for QuantumWalkSearch.ApproxRAA.sin_three_mul_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @elem
-- created : 2026-10-10T01:05:17.511138+00:00
-- url     : https://prove2.me/submissions/2be07e0e-105c-4d86-91f8-dcfefde0b170

import Mathlib

theorem solution (A B : ℝ) (hA : A ∈ Set.Icc 0 (Real.pi / 4))
    (hB : B ∈ Set.Icc 0 (Real.pi / 4)) :
    |Real.sin (3 * A) - Real.sin (3 * B)| ≤ 3 * |Real.sin A - Real.sin B| := by
  obtain ⟨hA0, hA1⟩ := hA
  obtain ⟨hB0, hB1⟩ := hB
  have hpi := Real.pi_pos
  -- sin² ≤ 1/2 on [0, π/4]
  have hsq : ∀ x : ℝ, 0 ≤ x → x ≤ Real.pi / 4 → Real.sin x ^ 2 ≤ 1 / 2 := by
    intro x hx0 hx1
    have hcos : Real.cos (Real.pi / 4) ≤ Real.cos x :=
      Real.cos_le_cos_of_nonneg_of_le_pi hx0 (by linarith) hx1
    rw [Real.cos_pi_div_four] at hcos
    have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hc0 : 0 ≤ Real.sqrt 2 / 2 := by positivity
    have hcsq : (Real.sqrt 2 / 2) ^ 2 ≤ Real.cos x ^ 2 := by gcongr
    have : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by rw [div_pow, hs2]; norm_num
    have hid := Real.sin_sq_add_cos_sq x
    linarith
  have hsA := hsq A hA0 hA1
  have hsB := hsq B hB0 hB1
  rw [Real.sin_three_mul, Real.sin_three_mul]
  set s := Real.sin A with hs
  set t := Real.sin B with ht
  have hfac : 3 * s - 4 * s ^ 3 - (3 * t - 4 * t ^ 3) =
      (s - t) * (3 - 4 * (s ^ 2 + s * t + t ^ 2)) := by ring
  rw [hfac, abs_mul, mul_comm]
  apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg (s - t), sq_nonneg (s + t)]
