-- Prove2me | solution 1 for ShiOptRates.Stochastic.exists_le_of_expectedDescent
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-08T22:52:16.780137+00:00
-- url     : https://prove2.me/submissions/a248f662-6223-4aab-ba14-7694c0e6a896

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
import Theorems.Thm_ShiOptRates_Stochastic_sum_le_of_expectedDescent
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

theorem solution {astar : ℝ} (hh : 0 < h) (hK : 0 < K)
    (hrec : ExpectedDescent a b h L σ K) (hlow : astar ≤ a K) :
    ∃ k < K, b k ≤ 2 * (a 0 - astar) / (h * K) + L * h * σ ^ 2 := by
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  set R : ℝ := 2 * (a 0 - astar) / (h * K) + L * h * σ ^ 2 with hR
  have htel := sum_le_of_expectedDescent hrec
  -- bound the sum, then average
  have hsum : h / 2 * ∑ k ∈ range K, b k
      ≤ (a 0 - astar) + K * (L * h ^ 2 * σ ^ 2 / 2) := by
    have : a 0 - a K ≤ a 0 - astar := by linarith
    linarith
  have hconst : ∑ _k ∈ range K, R = K * R := by
    rw [Finset.sum_const, card_range, nsmul_eq_mul]
  have hRsum : h / 2 * ((K : ℝ) * R) = (a 0 - astar) + K * (L * h ^ 2 * σ ^ 2 / 2) := by
    rw [hR]
    field_simp
  have hle : ∑ k ∈ range K, b k ≤ ∑ _k ∈ range K, R := by
    rw [hconst]
    have h2 : h / 2 * ∑ k ∈ range K, b k ≤ h / 2 * ((K : ℝ) * R) := by
      rw [hRsum]; exact hsum
    exact le_of_mul_le_mul_left h2 (by linarith)
  obtain ⟨k, hk, hklt⟩ :=
    Finset.exists_le_of_sum_le (nonempty_range_iff.mpr hK.ne') hle
  exact ⟨k, mem_range.mp hk, hklt⟩

end
