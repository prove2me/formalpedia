-- Prove2me | solution 1 for ShiOptRates.pl_rate
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-08T23:02:53.052389+00:00
-- url     : https://prove2.me/submissions/40e20005-15c4-4466-bf18-fff30cc22987

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
import Theorems.Thm_ShiOptRates_pl_step
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

theorem solution (hL : 0 < L) (hmu : 0 < mu) (hmuL : mu ≤ L) (hQ : QuadUpper f g L)
    (hPL : PolyakLojasiewicz f g mu fstar) {δ : ℝ} (_hδ : 0 ≤ δ)
    (x gd : ℕ → E) (K : ℕ)
    (hstep : ∀ k < K, x (k + 1) = x k - L⁻¹ • gd k)
    (herr : ∀ k < K, ‖gd k - g (x k)‖ ≤ δ) :
    f (x K) - fstar
      ≤ (1 - mu / L) ^ K * (f (x 0) - fstar) + δ ^ 2 / (2 * mu) * (1 - (1 - mu / L) ^ K) := by
  have hρ0 : (0 : ℝ) ≤ 1 - mu / L := by
    have : mu / L ≤ 1 := by rw [div_le_one hL]; exact hmuL
    linarith
  have hfloor : δ ^ 2 / (2 * L) = δ ^ 2 / (2 * mu) * (mu / L) := by
    field_simp
  induction K with
  | zero => simp
  | succ n ih =>
      have hn : ∀ k < n, x (k + 1) = x k - L⁻¹ • gd k := fun k hk => hstep k (by omega)
      have hn' : ∀ k < n, ‖gd k - g (x k)‖ ≤ δ := fun k hk => herr k (by omega)
      have hprev := ih hn hn'
      have hone := pl_step hL hmu hQ hPL (x n) (gd n) (herr n (by omega))
      rw [← hstep n (by omega)] at hone
      -- `a_{n+1} ≤ ρ a_n + δ²/(2L)`, then substitute the inductive bound
      have hmul : (1 - mu / L) * (f (x n) - fstar)
          ≤ (1 - mu / L) * ((1 - mu / L) ^ n * (f (x 0) - fstar)
              + δ ^ 2 / (2 * mu) * (1 - (1 - mu / L) ^ n)) :=
        mul_le_mul_of_nonneg_left hprev hρ0
      have hexp : (1 - mu / L) * ((1 - mu / L) ^ n * (f (x 0) - fstar)
            + δ ^ 2 / (2 * mu) * (1 - (1 - mu / L) ^ n)) + δ ^ 2 / (2 * L)
          = (1 - mu / L) ^ (n + 1) * (f (x 0) - fstar)
            + δ ^ 2 / (2 * mu) * (1 - (1 - mu / L) ^ (n + 1)) := by
        rw [hfloor, pow_succ]
        ring
      linarith [hone, hmul, hexp.le, hexp.ge]

end
