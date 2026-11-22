-- Prove2me | solution 1 for ShiOptRates.pl_step
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-08T22:55:06.594423+00:00
-- url     : https://prove2.me/submissions/d8482c67-14b3-4abe-9c42-4b8015d919ad

/-
Derived from lean-optrates -- https://github.com/shiy1022/lean-optrates
  commit 4c0b84980914ea7f9007510d92bcd60e91ad8448
  file   Optrates/PL.lean
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
import Theorems.Thm_ShiOptRates_descent_step
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
# Linear convergence under Polyak–Łojasiewicz

Until this file, `PolyakLojasiewicz` and `QuadLower` were *defined* but consumed by no rate
theorem: the library proved exactly one criterion, `min_k ‖∇f(x_k)‖ ≤ ε`.  This adds the
second, and it is the one a classical optimization audience asks for first — linear
convergence of the *function value* — under the same inexact oracle.

The result has the shape every noisy linearly-convergent method has: a geometric term that
decays and a noise floor that does not.

`f(x_K) - f⋆ ≤ (1 - μ/L)^K (f(x_0) - f⋆) + δ²/(2μ)`

Both constants are exact, and the induction establishing it is an equality at the inductive
step — `δ²/(2L) = (δ²/(2μ))(1 - ρ)` — so nothing is lost.

Note where `μ` sits: the noise floor is `δ²/(2μ)`, not `δ²/(2L)`. Ill-conditioning hurts
the floor, not just the rate; requesting accuracy `δ = √(μ ε)` is what buys `ε` of function
value, so the *cost* of a PL rate scales with the condition number through the oracle, not
only through the iteration count.

## Main results

* `pl_step` — one step: `a_{k+1} ≤ (1 - μ/L) a_k + δ_k²/(2L)` where `a_k = f(x_k) - f⋆`.
* `pl_rate` — the geometric recursion solved, with the noise floor.
* `pl_gap_le` — the `ε`-form: `δ ≤ √(μ ε)` and `ρ^K a_0 ≤ ε/2` give `f(x_K) - f⋆ ≤ ε`.
-/

section
open ShiOptRates

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → ℝ} {g : E → E} {L mu fstar : ℝ}

theorem solution (hL : 0 < L) (_hmu : 0 < mu) (hQ : QuadUpper f g L)
    (hPL : PolyakLojasiewicz f g mu fstar) (x gd : E) {δ : ℝ}
    (herr : ‖gd - g x‖ ≤ δ) :
    f (x - L⁻¹ • gd) - fstar ≤ (1 - mu / L) * (f x - fstar) + δ ^ 2 / (2 * L) := by
  have hstep := descent_step hL hQ x gd
  have hsq : ‖gd - g x‖ ^ 2 ≤ δ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) herr 2
  have hpl := hPL x
  -- `2 mu (f x - f⋆) ≤ ‖g x‖² ≤ 2L (f x - f x⁺) + δ²`
  have hcomb : 2 * mu * (f x - fstar) ≤ 2 * L * (f x - f (x - L⁻¹ • gd)) + δ ^ 2 := by
    linarith [hstep, hsq, hpl]
  -- divide by `2L`
  have hdiv : mu / L * (f x - fstar) ≤ (f x - f (x - L⁻¹ • gd)) + δ ^ 2 / (2 * L) := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hL]
    have h2 : δ ^ 2 / (2 * L) * L = δ ^ 2 / 2 := by field_simp
    nlinarith [hcomb, h2]
  linarith [hdiv]

end
