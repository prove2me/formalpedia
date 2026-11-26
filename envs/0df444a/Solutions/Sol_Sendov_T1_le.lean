-- Prove2me | solution 1 for Sendov.T1_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:58:58.240671+00:00
-- url     : https://prove2.me/submissions/e2ced565-552a-4a8e-ae64-8f94b215e5e8

import Definitions.Def_Sendov_LargeDegree_Tail
import Definitions.Def_Sendov_LargeDegree_Monotone
import Theorems.Thm_Sendov_tail1_poly
import Theorems.Thm_Sendov_c_mono
import Theorems.Thm_Sendov_c_ge_of_large
import Theorems.Thm_Sendov_three_add_pos


set_option autoImplicit false
open Sendov
variable {n : ℕ} {α : ℝ}
namespace Sendov
theorem _root_.solution (hn : 101 ≤ n) (hα : 0 ≤ α) (hα' : α ≤ 17) :
    T1 n α ≤ 101 / 100 * T1 101 α := by
  have h3 : (0 : ℝ) < 3 + α := three_add_pos hα
  have hnR : (101 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hc1 : (0 : ℝ) < c 101 α := by
    have := c_ge_of_large (n := 101) le_rfl hα hα'
    linarith
  have hcn : c 101 α ≤ c n α := c_mono (by omega) hn hα
  have hcnp : (0 : ℝ) < c n α := lt_of_lt_of_le hc1 hcn
  have hc4 : c 101 α ^ 4 ≤ c n α ^ 4 := by
    exact pow_le_pow_left₀ hc1.le hcn 4
  have hN : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hN2 : (0 : ℝ) < (n : ℝ) + 2 := by linarith
  have hN4 : (0 : ℝ) < (n : ℝ) + 4 := by linarith
  have hprod : (0 : ℝ) ≤ ((n : ℝ) - 1) * ((n : ℝ) + 2) * ((n : ℝ) + 4) :=
    mul_nonneg (mul_nonneg hN.le hN2.le) hN4.le
  have hD1 : (0 : ℝ) < (3 + α) * c 101 α ^ 4 * ((n : ℝ) - 1) * ((n : ℝ) + 2) * ((n : ℝ) + 4) :=
    mul_pos (mul_pos (mul_pos (mul_pos h3 (pow_pos hc1 4)) hN) hN2) hN4
  have hDle : (3 + α) * c 101 α ^ 4 * ((n : ℝ) - 1) * ((n : ℝ) + 2) * ((n : ℝ) + 4)
      ≤ (3 + α) * c n α ^ 4 * ((n : ℝ) - 1) * ((n : ℝ) + 2) * ((n : ℝ) + 4) := by
    have hd : (0 : ℝ) ≤ (3 + α) * (c n α ^ 4 - c 101 α ^ 4) *
        (((n : ℝ) - 1) * ((n : ℝ) + 2) * ((n : ℝ) + 4)) :=
      mul_nonneg (mul_nonneg h3.le (by linarith)) hprod
    nlinarith [hd]
  -- step A: enlarge the denominator's `c` from `c n` down to `c 101`
  have stepA : T1 n α
      ≤ 24 * ((n : ℝ) - 1 - 2 * α) ^ 2 /
          ((3 + α) * c 101 α ^ 4 * ((n : ℝ) - 1) * ((n : ℝ) + 2) * ((n : ℝ) + 4)) := by
    rw [T1]
    exact div_le_div_of_nonneg_left (by positivity) hD1 hDle
  refine stepA.trans ?_
  -- step B: the certificate, with the same `c 101` on both sides
  have hT101 : T1 101 α = 24 * (100 - 2 * α) ^ 2 / ((3 + α) * c 101 α ^ 4 * 1081500) := by
    simp only [T1]
    norm_num
    ring_nf
  have hD2 : (0 : ℝ) < 100 * ((3 + α) * c 101 α ^ 4 * 1081500) := by
    have h4 := pow_pos hc1 4
    positivity
  have hRHS : 101 / 100 * T1 101 α
      = 101 * (24 * (100 - 2 * α) ^ 2) / (100 * ((3 + α) * c 101 α ^ 4 * 1081500)) := by
    rw [hT101]
    field_simp
  rw [hRHS, div_le_div_iff₀ hD1 hD2]
  have hj : (0 : ℝ) ≤ (n : ℝ) - 101 := by linarith
  have hcert := tail1_poly (j := (n : ℝ) - 101) hj hα hα'
  have hscale : (0 : ℝ) ≤ 24 * (3 + α) * c 101 α ^ 4 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hcert hscale]
end Sendov
