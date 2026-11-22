-- Prove2me | solution 1 for ShiOptRates.Stochastic.exists_le_sq_of_stepsize
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-08T23:01:20.206649+00:00
-- url     : https://prove2.me/submissions/721f59f6-bf10-4d01-869f-18057424516c

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
import Theorems.Thm_ShiOptRates_Stochastic_exists_le_of_expectedDescent
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

theorem solution {astar ε : ℝ} (hε : 0 < ε) (hL : 0 < L) (hσ : 0 < σ)
    (hK : 0 < K)
    (hrec : ExpectedDescent a b (ε ^ 2 / (2 * L * σ ^ 2)) L σ K)
    (hlow : astar ≤ a K)
    (hKbig : 8 * L * (a 0 - astar) * σ ^ 2 / ε ^ 4 ≤ (K : ℝ)) :
    ∃ k < K, b k ≤ ε ^ 2 := by
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hL' : L ≠ 0 := hL.ne'
  have hσ' : σ ≠ 0 := hσ.ne'
  set hs : ℝ := ε ^ 2 / (2 * L * σ ^ 2) with hhs
  have hspos : 0 < hs := by rw [hhs]; positivity
  obtain ⟨k, hk, hbound⟩ := exists_le_of_expectedDescent hspos hK hrec hlow
  refine ⟨k, hk, ?_⟩
  -- the noise floor is exactly ε²/2
  have hfloor : L * hs * σ ^ 2 = ε ^ 2 / 2 := by
    rw [hhs]; field_simp
  -- the horizon hypothesis, denominators cleared
  have hK4 : 8 * L * (a 0 - astar) * σ ^ 2 ≤ (K : ℝ) * ε ^ 4 := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < ε ^ 4)] at hKbig
    linarith
  -- the optimization term is at most ε²/2
  have hopt : 2 * (a 0 - astar) / (hs * K) ≤ ε ^ 2 / 2 := by
    rw [div_le_iff₀ (mul_pos hspos hKR)]
    have hexp : ε ^ 2 / 2 * (hs * (K : ℝ)) = (K : ℝ) * ε ^ 4 / (4 * L * σ ^ 2) := by
      rw [hhs]; field_simp; ring
    rw [hexp, le_div_iff₀ (by positivity : (0:ℝ) < 4 * L * σ ^ 2)]
    nlinarith [hK4]
  linarith [hbound, hfloor, hopt]

end
