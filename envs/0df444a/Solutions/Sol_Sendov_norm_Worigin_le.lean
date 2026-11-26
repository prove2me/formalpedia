-- Prove2me | solution 1 for Sendov.norm_Worigin_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:06:11.162688+00:00
-- url     : https://prove2.me/submissions/206f64d1-d5b8-4490-841b-f4ea79c1908a

import Definitions.Def_Sendov_Analytic_Origin
import Definitions.Def_Sendov_Analytic_Jsum
import Definitions.Def_Sendov_Reduction_Setup
import Definitions.Def_Sendov_Analytic_OriginExact
import Theorems.Thm_Sendov_norm_mul_two_re_le
import Theorems.Thm_Sendov_Worigin_re
import Theorems.Thm_Sendov_Worigin_im

set_option autoImplicit false
open Sendov
open Complex (I)
namespace Sendov
theorem _root_.solution {n : ℕ} {a x y : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hn1 : (0 : ℝ) < (n : ℝ) - 1) (hxle : x ≤ 1) (hy2 : y ^ 2 ≤ 1 - x ^ 2) :
    ‖Worigin n a x y‖
      ≤ a ^ 2 * ((n : ℝ) - 1) + 1 - a * x + (1 - x ^ 2) / (2 * ((n : ℝ) - 1)) := by
  have hax : a * x ≤ a := mul_le_of_le_one_right (le_of_lt ha0) hxle
  have ha2 : (0 : ℝ) < a ^ 2 * ((n : ℝ) - 1) := by positivity
  have hslow : a ^ 2 * ((n : ℝ) - 1) ≤ a ^ 2 * ((n : ℝ) - 1) + 1 - a * x := by linarith
  have hpos : 0 < (Worigin n a x y).re := by rw [Worigin_re]; linarith
  have hs : (0 : ℝ) < 2 * (a ^ 2 * ((n : ℝ) - 1) + 1 - a * x) := by linarith
  have hden : (0 : ℝ) < 2 * ((n : ℝ) - 1) := by linarith
  have h := norm_mul_two_re_le hpos
  rw [Worigin_re, Worigin_im] at h
  have hmain : ‖Worigin n a x y‖
      ≤ (a ^ 2 * ((n : ℝ) - 1) + 1 - a * x)
        + a ^ 2 * y ^ 2 / (2 * (a ^ 2 * ((n : ℝ) - 1) + 1 - a * x)) := by
    rw [← sub_le_iff_le_add', le_div_iff₀ hs]
    nlinarith [h]
  have htail : a ^ 2 * y ^ 2 / (2 * (a ^ 2 * ((n : ℝ) - 1) + 1 - a * x))
      ≤ (1 - x ^ 2) / (2 * ((n : ℝ) - 1)) := by
    rw [div_le_div_iff₀ hs hden]
    nlinarith [hy2, hslow, ha2, sq_nonneg y, hn1]
  linarith [hmain, htail]
end Sendov
