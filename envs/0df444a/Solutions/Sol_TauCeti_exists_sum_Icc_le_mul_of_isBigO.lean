-- Prove2me | solution 1 for TauCeti.exists_sum_Icc_le_mul_of_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:24:34.129337+00:00
-- url     : https://prove2.me/submissions/1e0294d9-4ec5-4f58-8f18-6e2f47e72d9f

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Tactic.FieldSimp

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Linear growth of partial sums from a window bound

If nonnegative terms `f n` have sums over the multiplicative windows `q x < n ≤ x` bounded by a
multiple of `x`, for a fixed ratio `0 ≤ q < 1` and all large `x`, then their partial sums
`∑_{1 ≤ n ≤ x} f n` are `O(x)`: the partial sum up to `x` is the window sum plus the partial sum
up to `q x`, and the window bounds form a geometric series.

This is the summation step of Chebyshev-type bounds, where a local estimate on windows
`(q x, x]` comes from a smoothed average and the global linear bound is what is needed.

## Main results

* `TauCeti.isBigO_sum_Icc_of_sum_Ioc_floor_mul_le`: a window bound `O(x)` implies partial sums
  `O(x)`.
* `TauCeti.exists_sum_Icc_le_mul_of_isBigO`: partial sums that are `O(x)` are bounded by `C N`
  at every natural cutoff `N`, with one constant `C`.
-/

 section

open Asymptotics Filter

namespace TauCeti
end TauCeti
section TauCeti
open TauCeti



/-- **A uniform linear bound from linear growth.** If the partial sums `∑_{1 ≤ n ≤ x} f n`
are `O(x)`, then a single constant `C` bounds them by `C N` at every natural cutoff `N`, including
the finitely many cutoffs below the range where the `O(x)` estimate starts. -/
theorem solution {f : ℕ → ℝ}
    (h : (fun x : ℝ ↦ ∑ n ∈ _root_.Finset.Icc 1 ⌊x⌋₊, f n) =O[_root_.Filter.atTop] fun x ↦ x) :
    ∃ C : ℝ, ∀ N : ℕ, ∑ n ∈ _root_.Finset.Icc 1 N, f n ≤ C * N := by
  obtain ⟨c, hc⟩ := h.bound
  obtain ⟨x₀, hx₀⟩ := _root_.Filter.eventually_atTop.1 hc
  set S : ℕ → ℝ := fun N ↦ ∑ n ∈ _root_.Finset.Icc 1 N, f n with hS
  set B : ℝ := ∑ n ∈ _root_.Finset.Icc 1 ⌈x₀⌉₊, ‖f n‖ with hB
  have hBnn : 0 ≤ B := _root_.Finset.sum_nonneg fun _ _ ↦ _root_.norm_nonneg _
  refine ⟨_root_.Max.max c B, fun N ↦ ?_⟩
  have hN0 : (0 : ℝ) ≤ N := N.cast_nonneg
  rcases _root_.le_or_gt ⌈x₀⌉₊ N with hN | hN
  · have hbound := hx₀ N ((_root_.Nat.le_ceil x₀).trans (_root_.Nat.cast_le.2 hN))
    rw [_root_.Nat.floor_natCast, _root_.Real.norm_of_nonneg hN0] at hbound
    have hSnorm : S N ≤ ‖S N‖ := by
      simpa only [_root_.Real.norm_eq_abs] using _root_.le_abs_self (S N)
    exact hSnorm.trans (hbound.trans (_root_.mul_le_mul_of_nonneg_right (_root_.le_max_left _ _) hN0))
  · rcases _root_.Nat.eq_zero_or_pos N with rfl | hNpos
    · simp
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
    calc S N ≤ ∑ n ∈ _root_.Finset.Icc 1 N, ‖f n‖ :=
          _root_.Finset.sum_le_sum fun n _ ↦ by
            simpa only [_root_.Real.norm_eq_abs] using _root_.le_abs_self (f n)
      _ ≤ B := _root_.Finset.sum_le_sum_of_subset_of_nonneg (_root_.Finset.Icc_subset_Icc_right hN.le)
        fun _ _ _ ↦ _root_.norm_nonneg _
      _ ≤ B * N := _root_.le_mul_of_one_le_right hBnn hN1
      _ ≤ _root_.Max.max c B * N := _root_.mul_le_mul_of_nonneg_right (_root_.le_max_right _ _) hN0

end TauCeti

end
end
