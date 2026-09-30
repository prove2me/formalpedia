-- Prove2me | solution 1 for Real.neg_log_one_sub_rpow_sub_le_div
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:27:24.143873+00:00
-- url     : https://prove2.me/submissions/ee79244b-4919-46ba-a201-a9fb439b69d3

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Theorems.Thm_Real_neg_log_one_sub_sub_le

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Elementary bounds on `-log (1 - x)`

This file bounds the quadratic remainder `-log (1 - x) - x`, then specializes the estimate to
`x = y ^ (-s)`. The sharp factor `2` in the denominator comes from reading Mathlib's complex
logarithm bound along the reals. It also records the coarser estimate
`-log (1 - x) ≤ x + 2 x ^ 2` for `0 ≤ x ≤ 1/2`.

## Main results

* `Real.neg_log_one_sub_sub_le`: for `0 ≤ x < 1`, the remainder is at most
  `x² / (2 (1 - x))`.
* `Real.neg_log_one_sub_rpow_sub_le_div`: for `2 ≤ y` and `0 < s`, it is at most
  `y ^ (-2s) / (2 (1 - 2 ^ (-s)))`.
* `Real.neg_log_one_sub_rpow_sub_le`: for `2 ≤ y` and `1 ≤ s`, it is at most `y⁻²`.
* `Real.neg_log_one_sub_le_add_two_mul_sq`: for `0 ≤ x ≤ 1/2`, `-log (1 - x)` is at most
  `x + 2 x ^ 2`.
* `Complex.norm_neg_log_one_sub_sub_le`: for complex `z` with `‖z‖ ≤ 1/2`, the remainder
  `-log (1 - z) - z` has norm at most `‖z‖ ^ 2`.

## References

The shape of `Real.neg_log_one_sub_sub_le` follows the private declaration
`neg_log_one_sub_sub_le` in `CebotarevDensity/Density.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
C. Birkbeck and R. Brasca), commit `8575c9df1ae0a61120ab5c964c7911414254bec7`. The sharper
constant here comes from Mathlib's `Complex.norm_log_one_sub_inv_sub_self_le`.
-/

 section

namespace Real
end Real
section Real
open Real







/-- For `2 ≤ y` and `0 < s`, the quadratic remainder of `-log (1 - y ^ (-s))` is bounded by
`y ^ (-2s) / (2 (1 - 2 ^ (-s)))`. -/
theorem solution {y s : ℝ} (hy : 2 ≤ y) (hs : 0 < s) :
    -_root_.Real.log (1 - y ^ (-s)) - y ^ (-s) ≤
      y ^ (-(2 * s)) / (2 * (1 - (2 : ℝ) ^ (-s))) := by
  have hy0 : (0 : ℝ) < y := by linarith
  have hxle : y ^ (-s) ≤ (2 : ℝ) ^ (-s) :=
    _root_.Real.rpow_le_rpow_of_nonpos _root_.two_pos hy (by linarith)
  have h2lt : (2 : ℝ) ^ (-s) < 1 :=
    _root_.Real.rpow_lt_one_of_one_lt_of_neg _root_.one_lt_two (by linarith)
  calc
    -_root_.Real.log (1 - y ^ (-s)) - y ^ (-s) ≤
        (y ^ (-s)) ^ 2 / (2 * (1 - y ^ (-s))) :=
      _root_.Real.neg_log_one_sub_sub_le (_root_.Real.rpow_nonneg hy0.le _) (hxle.trans_lt h2lt)
    _ ≤ (y ^ (-s)) ^ 2 / (2 * (1 - (2 : ℝ) ^ (-s))) := by
      gcongr
    _ = y ^ (-(2 * s)) / (2 * (1 - (2 : ℝ) ^ (-s))) := by
      rw [_root_.pow_two, ← _root_.Real.rpow_add hy0, ← _root_.two_mul, _root_.mul_neg]





end Real

namespace Complex
end Complex
section Complex
open Complex



end Complex

end
end
