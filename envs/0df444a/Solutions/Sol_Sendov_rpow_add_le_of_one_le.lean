-- Prove2me | solution 1 for Sendov.rpow_add_le_of_one_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:00:34.97625+00:00
-- url     : https://prove2.me/submissions/439436d0-a867-4acc-8f41-07e16abae8c2

import Definitions.Def_Sendov_Reduction_Stat
import Definitions.Def_Sendov_Reduction_Simplified

set_option autoImplicit false
open Sendov
open MeasureTheory
variable {n : ℕ} {a x t α : ℝ}
namespace Sendov
theorem _root_.solution {P Q p : ℝ} (hP : 0 ≤ P) (hPQ : 0 < P + Q) (hp : 1 ≤ p) :
    (P + Q) ^ p ≤ P ^ p + p * Q * (P + Q) ^ (p - 1) := by
  have hθ : (0 : ℝ) ≤ P / (P + Q) := div_nonneg hP hPQ.le
  have hb := one_add_mul_self_le_rpow_one_add (s := P / (P + Q) - 1) (by linarith) hp
  rw [show (1 : ℝ) + (P / (P + Q) - 1) = P / (P + Q) by ring] at hb
  have hpow : (0 : ℝ) < (P + Q) ^ p := Real.rpow_pos_of_pos hPQ p
  have hfrac : (P / (P + Q)) ^ p * (P + Q) ^ p = P ^ p := by
    rw [← Real.mul_rpow hθ hPQ.le]
    congr 1
    field_simp
  have hsub : (P + Q) ^ (p - 1) = (P + Q) ^ p / (P + Q) := by
    rw [Real.rpow_sub hPQ, Real.rpow_one]
  have key : (P + Q) ^ p - p * Q * ((P + Q) ^ p / (P + Q)) ≤ P ^ p := by
    calc (P + Q) ^ p - p * Q * ((P + Q) ^ p / (P + Q))
        = (1 + p * (P / (P + Q) - 1)) * (P + Q) ^ p := by
          field_simp
          ring
      _ ≤ (P / (P + Q)) ^ p * (P + Q) ^ p := mul_le_mul_of_nonneg_right hb hpow.le
      _ = P ^ p := hfrac
  rw [hsub]
  linarith
end Sendov
