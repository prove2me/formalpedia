-- Prove2me | solution 1 for TauCeti.tsum_nat_rpow_neg_le_two
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:16:24.73093+00:00
-- url     : https://prove2.me/submissions/6ec6b029-9207-4ac7-95c9-3c8fb238ba83

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ZetaValues

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# A clean constant bound for the `p`-series beyond exponent two

`∑' m : ℕ, m ^ (-t) ≤ 2` for every real `t ≥ 2`. Mathlib supplies the exact value at the endpoint,
`ζ (2) = π ^ 2 / 6`, and summability throughout `t > 1`, but no inequality valid across a range of
exponents; that is what this file adds.

The bound is deliberately lossy. The supremum over `t ≥ 2` is `ζ (2) = 1.6449…`, so `2` gives away
about 18%. A round constant is the useful thing to expose: consumers carry it through chains of
inequalities and none of them wants `π` in the goal.

Nothing here is specific to any application, and the file contains no number theory. The `m = 0`
term is `0`, by the junk value of `0 ^ (-t)`.

## Main results

* `TauCeti.tsum_nat_rpow_neg_le_two` — `∑' m : ℕ, m ^ (-t) ≤ 2` for `2 ≤ t`.
-/

 section

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti

/-- **The `p`-series over `ℕ` is at most `2` beyond exponent two.** For `2 ≤ t`,
`∑' m : ℕ, m ^ (-t) ≤ 2`, the case `t = 2` being `ζ(2) = π ^ 2 / 6 < 2`.  The `m = 0` term is
`0`, by the junk value of `0 ^ (-t)`. -/
theorem solution {t : ℝ} (ht : 2 ≤ t) : ∑' m : ℕ, (m : ℝ) ^ (-t) ≤ 2 := by
  have hsum : ∀ u : ℝ, 1 < u → _root_.Summable fun m : ℕ ↦ (m : ℝ) ^ (-u) := fun u hu ↦
    Real.summable_nat_rpow.mpr (by linarith)
  have hfun : (fun m : ℕ ↦ (m : ℝ) ^ (-(2 : ℝ))) = fun m : ℕ ↦ (1 : ℝ) / (m : ℝ) ^ 2 := by
    funext m
    rw [_root_.Real.rpow_neg (_root_.Nat.cast_nonneg m), _root_.Real.rpow_two, _root_.one_div]
  have hzeta : ∑' m : ℕ, (m : ℝ) ^ (-(2 : ℝ)) = _root_.Real.pi ^ 2 / 6 := by
    rw [hfun]
    exact hasSum_zeta_two.tsum_eq
  refine _root_.le_trans (_root_.Summable.tsum_le_tsum (fun m ↦ ?_) (hsum t (by linarith))
    (hsum 2 _root_.one_lt_two)) ?_
  · rcases _root_.Nat.eq_zero_or_pos m with rfl | hm
    · rw [_root_.Nat.cast_zero, _root_.Real.zero_rpow (by linarith), _root_.Real.zero_rpow (by norm_num)]
    · exact _root_.Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm) (by linarith)
  · rw [hzeta]
    nlinarith [_root_.Real.pi_lt_d2, _root_.Real.pi_pos]

end TauCeti


end
end
