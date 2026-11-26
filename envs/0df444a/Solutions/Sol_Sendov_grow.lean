-- Prove2me | solution 1 for Sendov.grow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:05:02.88587+00:00
-- url     : https://prove2.me/submissions/854ac1f2-5d0d-4085-a7c3-105607825f6f

import Definitions.Def_Sendov_Analytic_Origin
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_OriginExact
import Theorems.Thm_Sendov_Worigin_re

set_option autoImplicit false
open Sendov
open Complex (I)
namespace Sendov
theorem _root_.solution {n : ℕ} (hn : 5 ≤ n) {a x y : ℝ} (ha0 : 0 < a) (hx : x ≤ 1) :
    2 * a * (n : ℝ) / ((n : ℝ) - 1) ≤ ‖Worigin n a x y‖ := by
  have hnR : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hu : (0 : ℝ) ≤ (n : ℝ) - 5 := by linarith
  have hdisc : 0 < 4 * ((n : ℝ) - 1) ^ 3 - (3 * (n : ℝ) - 1) ^ 2 := by
    nlinarith [hu, sq_nonneg ((n : ℝ) - 5), mul_nonneg (mul_nonneg hu hu) hu]
  have hquad : 0 < ((n : ℝ) - 1) ^ 2 * a ^ 2 - (3 * (n : ℝ) - 1) * a + ((n : ℝ) - 1) := by
    nlinarith [sq_nonneg (2 * ((n : ℝ) - 1) ^ 2 * a - (3 * (n : ℝ) - 1)), hdisc,
      mul_pos hn1 hn1]
  have hre : 2 * a * (n : ℝ) / ((n : ℝ) - 1) ≤ (Worigin n a x y).re := by
    rw [Worigin_re, div_le_iff₀ hn1]
    nlinarith [hquad, mul_nonneg (mul_nonneg (le_of_lt ha0) (sub_nonneg.2 hx)) (le_of_lt hn1)]
  exact hre.trans (Complex.re_le_norm _)
end Sendov
