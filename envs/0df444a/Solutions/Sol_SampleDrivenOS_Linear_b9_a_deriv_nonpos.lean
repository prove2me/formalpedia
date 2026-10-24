-- Prove2me | solution 1 for SampleDrivenOS.Linear.b9_a_deriv_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T13:48:38.50999+00:00
-- url     : https://prove2.me/submissions/4aa37432-8838-48a1-9dac-a9cb8a3fa1a3

import Mathlib
import Definitions.Def_SampleDrivenOS_Linear_Setting
import Theorems.Thm_SampleDrivenOS_Linear_b9_deriv_a
import Theorems.Thm_SampleDrivenOS_Linear_b9_b_ge
import Theorems.Thm_SampleDrivenOS_Linear_b9_c_le

set_option autoImplicit false
open SampleDrivenOS.Linear

theorem solution (s : ℝ) (hs : SampleDrivenOS.Limit.IsAlphaStar s) (hs' : s ∈ Set.Icc (0.74 : ℝ) 0.75)
    (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ d : ℝ, HasDerivAt (aB9 s) d p ∧ d ≤ 0 := by
  have hs01 : s ∈ Set.Ioo (0 : ℝ) 1 := ⟨hs.1, hs.2.1⟩
  refine ⟨2 * s * (1 - p) - bB9 s p + cB9 s p, (b9_deriv_a s hs01 p hp).2, ?_⟩
  have hb := b9_b_ge s hs01 p hp
  have hc := b9_c_le s hs hs' p hp
  obtain ⟨hp0, hp1⟩ := hp
  have hs0 := hs.1
  -- `2s(1-p) - 1/p + 1/p - s(1-p)(1+1/p) = s(1-p)(1 - 1/p) ≤ 0`
  have e : 2 * s * (1 - p) - 1 / p + (1 / p - s * (1 - p) * (1 + 1 / p)) =
      s * (1 - p) * (1 - 1 / p) := by ring
  have h1 : 1 - 1 / p ≤ 0 := by
    have : 1 ≤ 1 / p := by rw [le_div_iff₀ hp0]; linarith
    linarith
  have h2 : 0 ≤ s * (1 - p) := mul_nonneg hs0.le (by linarith)
  have h3 : s * (1 - p) * (1 - 1 / p) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos h2 h1
  linarith
