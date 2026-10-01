-- Prove2me | solution 1 for burau_cf_std_neg_self
-- status  : ACCEPTED   (prove)
-- author  : @lt9
-- created : 2026-09-30T22:17:09.518606+00:00
-- url     : https://prove2.me/submissions/f80f6b64-7096-496a-b3eb-a5a1b6887cb4

import Definitions.Def_burau_std_cf

set_option autoImplicit false

/-- Base case of the `-1/x` rule: for `x = 1` (`b = a`), `-1/x = -1` and the expansion is `[-1]`. -/
theorem solution (a : ℤ) (ha : a ≠ 0) : cfStd a (-a) = [-1] := by
  have hdiv : (-a) / a = -1 := by
    calc (-a) / a = (0 + a * (-1)) / a := by
          congr 1
          ring
      _ = 0 / a + (-1) := by rw [Int.add_mul_ediv_left 0 (-1) ha]
      _ = 0 + (-1) := by rw [Int.zero_ediv]
      _ = -1 := by ring
  have hmod : (-a) % a = 0 := by
    calc (-a) % a = (0 + a * (-1)) % a := by
          congr 2
          ring
      _ = 0 % a := by rw [Int.add_mul_emod_self_left]
      _ = 0 := Int.zero_emod a
  rw [cfStd_cons a (-a) ha, hdiv, hmod, cfStd_zero]
