-- Prove2me | solution 1 for SampleDrivenOS.Linear.b9_c_le
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T13:48:37.651662+00:00
-- url     : https://prove2.me/submissions/ed200dcf-cd7b-41c2-8f21-79ccc78e787c

import Mathlib
import Definitions.Def_SampleDrivenOS_Linear_Setting
import Theorems.Thm_SampleDrivenOS_Linear_b9_c_le_integral
import Theorems.Thm_SampleDrivenOS_Linear_b9_integral_bound
import Theorems.Thm_SampleDrivenOS_Linear_b9_numerical

set_option autoImplicit false
open SampleDrivenOS.Linear

theorem solution (s : ℝ) (hs : SampleDrivenOS.Limit.IsAlphaStar s) (hs' : s ∈ Set.Icc (0.74 : ℝ) 0.75) (p : ℝ)
    (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    cB9 s p ≤ 1 / p - s * (1 - p) * (1 + 1 / p) := by
  have h1 := b9_c_le_integral s ⟨hs.1, hs.2.1⟩ p hp
  have h2 := b9_integral_bound s hs p hp
  have h3 := b9_numerical s hs' p hp
  obtain ⟨hp0, hp1⟩ := hp
  set T := (1 / (p * s) - 1 / Real.exp 1) *
      Real.log ((1 / (p * s) + p / Real.exp 1) / (1 / (p * s) + p / Real.exp 1 - 1)) with hT
  have hsT : s ≤ T := by linarith [hs'.2]
  have hq : 0 ≤ (1 - p) / p := div_nonneg (by linarith) hp0.le
  have key : (1 - p) / p * s ≤ (1 - p) / p * T := mul_le_mul_of_nonneg_left hsT hq
  have e : s * (1 - p) * (1 + 1 / p) = s * (1 - p) + (1 - p) / p * s := by
    field_simp
  rw [e]
  linarith
