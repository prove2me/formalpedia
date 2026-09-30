-- Prove2me | solution 1 for Real.neg_log_one_sub_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:16:21.955572+00:00
-- url     : https://prove2.me/submissions/dcf14e42-61e2-4783-9df7-816e1bb59883

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real

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



/-- The quadratic remainder of `-log (1 - x)` is at most `x² / (2 (1 - x))` for
`0 ≤ x < 1`. This is Mathlib's complex logarithm bound read along the reals. -/
theorem solution {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    -_root_.Real.log (1 - x) - x ≤ x ^ 2 / (2 * (1 - x)) := by
  have hpos : (0 : ℝ) < 1 - x := by linarith
  have hnx : ‖(x : ℂ)‖ = x := by rw [_root_.Complex.norm_real, _root_.Real.norm_of_nonneg hx0]
  have hz : ‖(x : ℂ)‖ < 1 := by rw [hnx]; exact hx1
  -- `1 - x` is a positive real, so the whole real-to-complex passage is the single conditional
  -- rewrite `Complex.ofReal_log`; `push_cast` and `ring` absorb the remaining coercions, so the
  -- step does not depend on the order in which the casts are unfolded.
  have hcast : _root_.Complex.log (1 - (x : ℂ))⁻¹ - (x : ℂ) = ((-_root_.Real.log (1 - x) - x : ℝ) : ℂ) := by
    rw [show (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) by push_cast; ring, ← _root_.Complex.ofReal_inv,
      ← _root_.Complex.ofReal_log (inv_pos.mpr hpos).le]
    push_cast [_root_.Real.log_inv]
    ring
  calc
    -_root_.Real.log (1 - x) - x ≤ |(-_root_.Real.log (1 - x) - x)| := _root_.le_abs_self _
    _ = ‖_root_.Complex.log (1 - (x : ℂ))⁻¹ - (x : ℂ)‖ := by
      rw [hcast, _root_.Complex.norm_real, _root_.Real.norm_eq_abs]
    _ ≤ ‖(x : ℂ)‖ ^ 2 * (1 - ‖(x : ℂ)‖)⁻¹ / 2 :=
      _root_.Complex.norm_log_one_sub_inv_sub_self_le hz
    _ = x ^ 2 / (2 * (1 - x)) := by rw [hnx]; field_simp









end Real

namespace Complex
end Complex
section Complex
open Complex



end Complex

end
end
