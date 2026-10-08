-- Prove2me | solution 1 for RhinViola.exponent_below_target_of_global_ceilings
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-04T22:42:42.451754+00:00
-- url     : https://prove2.me/submissions/5354c100-ad21-487a-a7df-e76a304e78ef

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem solution (a b : ℝ)
    (ha : a ≤ -(2635725669 : ℝ) / 1000000000)
    (hb : b ≤ (2067714200 : ℝ) / 1000000000) :
    (a - b) / (a + 2) < (7398537 : ℝ) / 1000000 := by
  have hd : a + 2 < 0 := by linarith
  apply (div_lt_iff_of_neg hd).2
  norm_num at ha hb ⊢ <;> linarith
