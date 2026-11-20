-- Prove2me | solution 1 for QEC.Distillation.BK05T.bk05TRecurrence_threshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T12:18:38.350179+00:00
-- url     : https://prove2.me/submissions/f16ad344-0838-4f9e-93e6-3c7526fc41f3

import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option autoImplicit false

theorem _root_.solution : (let epsilon : Real := ((1 - Real.sqrt (3 / 7 : Real)) / 2); (let z : Real := (epsilon ^ 5 + 5 * epsilon ^ 2 * (1 - epsilon) ^ 3) / 6; let o : Real := ((1 - epsilon) ^ 5 + 5 * epsilon ^ 3 * (1 - epsilon) ^ 2) / 6; z / (z + o))) = ((1 - Real.sqrt (3 / 7 : Real)) / 2) := by
  let epsilon : Real := ((1 - Real.sqrt (3 / 7 : Real)) / 2)
  let z : Real := (epsilon ^ 5 + 5 * epsilon ^ 2 * (1 - epsilon) ^ 3) / 6
  let o : Real := ((1 - epsilon) ^ 5 + 5 * epsilon ^ 3 * (1 - epsilon) ^ 2) / 6
  change z / (z + o) = epsilon
  have hsqrt_nonneg : 0 ≤ Real.sqrt (3 / 7 : Real) := Real.sqrt_nonneg _
  have hsqrt_sq : Real.sqrt (3 / 7 : Real) ^ 2 = 3 / 7 := Real.sq_sqrt (by norm_num)
  have hsqrt_lt_one : Real.sqrt (3 / 7 : Real) < 1 := by
    by_contra! h
    nlinarith only [hsqrt_sq, h, sq_nonneg (Real.sqrt (3 / 7 : Real) - 1)]
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    linarith only [hsqrt_lt_one]
  have hcomplement : 0 < 1 - epsilon := by
    dsimp [epsilon]
    linarith only [hsqrt_nonneg]
  have hz : 0 < z := by
    dsimp [z]
    positivity
  have ho : 0 < o := by
    dsimp [o]
    positivity
  have hpoly : 7 * epsilon ^ 2 - 7 * epsilon + 1 = 0 := by
    dsimp [epsilon]
    nlinarith only [hsqrt_sq]
  apply (div_eq_iff (ne_of_gt (add_pos hz ho))).2
  have hdiff : z - epsilon * (z + o) =
      -(epsilon * (1 - epsilon) * (1 - 2 * epsilon) *
        (7 * epsilon ^ 2 - 7 * epsilon + 1) / 6) := by
    dsimp [z, o]
    ring
  exact sub_eq_zero.mp (by
    simpa only [hpoly, mul_zero, neg_zero, zero_div] using hdiff)
