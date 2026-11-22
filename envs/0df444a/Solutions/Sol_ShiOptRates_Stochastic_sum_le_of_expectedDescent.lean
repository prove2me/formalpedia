-- Prove2me | solution 1 for ShiOptRates.Stochastic.sum_le_of_expectedDescent
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-08T22:44:33.384139+00:00
-- url     : https://prove2.me/submissions/13a60088-6bac-41c9-a442-f422d657caf8

/-
Derived from lean-optrates -- https://github.com/shiy1022/lean-optrates
  commit 4c0b84980914ea7f9007510d92bcd60e91ad8448
  file   Optrates/Stochastic/Recursion.lean
Original work Copyright (c) 2026 Yueheng Shi, released under the Apache License,
Version 2.0.  The original copyright and author notices are retained below.

MODIFICATIONS made for publication on Prove2me: declarations not reachable from
the published targets were removed by declaration-graph skeleton subtraction;
project imports were rewritten to platform `Definitions.Def_*` / `Theorems.Thm_*`
modules; the root namespace `OptRates` was renamed to `ShiOptRates`; the enclosing `namespace` is replaced by `section`+`open` and the target
theorem is renamed to `solution`; 
no statement or proof was otherwise altered.

Built against Mathlib (Apache-2.0) at revision 0df444a360eaa60ab8c11dca51a86af692955474.
-/
import Definitions.Def_ShiOptrates_Cost
import Definitions.Def_ShiOptrates_FunctionClass
import Definitions.Def_ShiOptrates_Stochastic_Recursion
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic



/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yueheng Shi
-/

/-!
# L3a — The expected-descent recursion

The part of the classical SGD analysis that is *not* probabilistic.  Every
expectation-based rate proof for a first-order method passes through a scalar recursion of
the form

`aₖ₊₁ ≤ aₖ - (h/2) bₖ + L h² σ² / 2`

where `aₖ = E f(xₖ)` and `bₖ = E‖∇f(xₖ)‖²`.  Establishing that recursion is the
probabilistic step (`Optrates.Stochastic.OneStep`); turning it into a rate is real
analysis, and is done here once.

Separating the two is what makes the `ε⁻⁴` bound auditable: the constant `8 L Δ₀ σ² / ε⁴`
below is a consequence of arithmetic on the recursion alone, and no martingale theory can
change it.

## Main results

* `sum_le_of_expectedDescent` — telescoping the recursion.
* `exists_le_of_expectedDescent` — `min_{k<K} bₖ ≤ 2Δ₀/(hK) + L h σ²`, the standard
  two-term bound with both terms explicit.
* `exists_le_sq_of_stepsize` — **GL3's arithmetic core**: at `h = ε²/(2Lσ²)` and
  `K ≥ 8 L Δ₀ σ² / ε⁴` some `bₖ ≤ ε²`.  Stepsize supplied and verified, not derived, per
  the library's convention.
-/

section
open ShiOptRates
open ShiOptRates.Stochastic

open Finset

variable {a b : ℕ → ℝ} {h L σ : ℝ} {K : ℕ}

theorem solution (hrec : ExpectedDescent a b h L σ K) :
    h / 2 * ∑ k ∈ range K, b k ≤ (a 0 - a K) + K * (L * h ^ 2 * σ ^ 2 / 2) := by
  have hstep : ∀ k ∈ range K,
      a (k + 1) - a k ≤ -(h / 2 * b k) + L * h ^ 2 * σ ^ 2 / 2 := by
    intro k hk
    have := hrec k (mem_range.mp hk)
    linarith
  have hsum : ∑ k ∈ range K, (a (k + 1) - a k)
      ≤ ∑ k ∈ range K, (-(h / 2 * b k) + L * h ^ 2 * σ ^ 2 / 2) :=
    Finset.sum_le_sum hstep
  have hleft : ∑ k ∈ range K, (a (k + 1) - a k) = a K - a 0 := Finset.sum_range_sub a K
  have hneg : ∑ k ∈ range K, -(h / 2 * b k) = -(h / 2) * ∑ k ∈ range K, b k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hright : ∑ k ∈ range K, (-(h / 2 * b k) + L * h ^ 2 * σ ^ 2 / 2)
      = -(h / 2 * ∑ k ∈ range K, b k) + K * (L * h ^ 2 * σ ^ 2 / 2) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, card_range, nsmul_eq_mul, hneg]
    ring
  rw [hleft, hright] at hsum
  linarith

end
