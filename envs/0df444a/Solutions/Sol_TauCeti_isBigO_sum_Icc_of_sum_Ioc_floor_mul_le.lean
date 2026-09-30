-- Prove2me | solution 1 for TauCeti.isBigO_sum_Icc_of_sum_Ioc_floor_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:24:35.847141+00:00
-- url     : https://prove2.me/submissions/6eed5fcf-f67c-4e50-b6da-50203c81218e

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

/-- **Summing windows.** If nonnegative terms `f n` have sums over the windows `q x < n ≤ x`
bounded by `K x` for all large `x`, where `0 ≤ q < 1` is a fixed ratio, then their partial sums
`∑_{1 ≤ n ≤ x} f n` are `O(x)`. -/
theorem solution {f : ℕ → ℝ} (hf : 0 ≤ f) {q K : ℝ}
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (h : ∀ᶠ x : ℝ in _root_.Filter.atTop, ∑ n ∈ _root_.Finset.Ioc ⌊q * x⌋₊ ⌊x⌋₊, f n ≤ K * x) :
    (fun x : ℝ ↦ ∑ n ∈ _root_.Finset.Icc 1 ⌊x⌋₊, f n) =O[_root_.Filter.atTop] fun x ↦ x := by
  obtain ⟨x₀, hx₀⟩ := _root_.Filter.eventually_atTop.1 h
  set S : ℝ → ℝ := fun x ↦ ∑ n ∈ _root_.Finset.Ioc 0 ⌊x⌋₊, f n with hS
  have hSmono : _root_.Monotone S := fun x y hxy ↦
    _root_.Finset.sum_le_sum_of_subset_of_nonneg (_root_.Finset.Ioc_subset_Ioc_right (_root_.Nat.floor_mono hxy))
      fun n _ _ ↦ hf n
  have hSnn : ∀ x, 0 ≤ S x := fun x ↦ _root_.Finset.sum_nonneg fun n _ ↦ hf n
  -- Beyond `x₁` we have `q x ≤ x - 1`, so peeling off the window `(q x, x]` lowers `⌊x⌋₊`.
  set x₁ : ℝ := _root_.Max.max x₀ (1 / (1 - q))
  have hq1' : 0 < 1 - q := by linarith
  set K' : ℝ := _root_.Max.max K 0 / (1 - q) with hK'
  have hK'nn : 0 ≤ K' := by positivity
  have hK'eq : K' * q + _root_.Max.max K 0 = K' := by
    rw [hK']
    field_simp
    ring
  have key : ∀ N : ℕ, ∀ x : ℝ, 0 ≤ x → ⌊x⌋₊ ≤ N → S x ≤ K' * x + S x₁ := by
    intro N
    induction N with
    | zero =>
      intro x hx hN
      have : S x = 0 := by simp [hS, _root_.Nat.le_zero.1 hN]
      rw [this]
      have := hSnn x₁
      positivity
    | succ N ih =>
      intro x hx hN
      rcases _root_.le_or_gt x x₁ with hxx | hxx
      · have := hSmono hxx
        have : 0 ≤ K' * x := by positivity
        linarith
      have hxx₀ : x₀ ≤ x := _root_.le_trans (_root_.le_max_left _ _) hxx.le
      have hxq : q * x ≤ x - 1 := by
        have h1 : 1 / (1 - q) < x := _root_.lt_of_le_of_lt (_root_.le_max_right _ _) hxx
        rw [_root_.div_lt_iff₀ hq1'] at h1
        nlinarith
      have hfloor : ⌊q * x⌋₊ ≤ N := by
        have h1 : ⌊q * x⌋₊ ≤ ⌊x - 1⌋₊ := _root_.Nat.floor_mono hxq
        rw [_root_.Nat.floor_sub_one] at h1
        omega
      have hqx : 0 ≤ q * x := by positivity
      have hsplit : S x = S (q * x) + ∑ n ∈ _root_.Finset.Ioc ⌊q * x⌋₊ ⌊x⌋₊, f n :=
        (_root_.Finset.sum_Ioc_consecutive f (_root_.Nat.zero_le _)
          (_root_.Nat.floor_mono (by nlinarith))).symm
      have hwin := hx₀ x hxx₀
      have hrec := ih (q * x) hqx hfloor
      have hK : K * x ≤ _root_.Max.max K 0 * x := _root_.mul_le_mul_of_nonneg_right (_root_.le_max_left _ _) hx
      calc S x ≤ K' * (q * x) + S x₁ + _root_.Max.max K 0 * x := by linarith
        _ = (K' * q + _root_.Max.max K 0) * x + S x₁ := by ring
        _ = K' * x + S x₁ := by rw [hK'eq]
  refine .of_bound (K' + S x₁) ?_
  filter_upwards [_root_.Filter.eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hS' : ∑ n ∈ _root_.Finset.Icc 1 ⌊x⌋₊, f n = S x := by
    simp only [hS, ← _root_.Finset.Icc_add_one_left_eq_Ioc, _root_.zero_add]
  rw [hS', _root_.Real.norm_of_nonneg (hSnn x), _root_.Real.norm_of_nonneg hx0]
  have := key ⌊x⌋₊ x hx0 _root_.le_rfl
  have := hSnn x₁
  nlinarith



end TauCeti

end
end
