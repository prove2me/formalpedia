-- Prove2me | solution 1 for ShiOptRates.Stochastic.accumulation_sq
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-08T22:42:35.239043+00:00
-- url     : https://prove2.me/submissions/dd47d307-44ce-47a3-896c-ca8b8bebd302

/-
Derived from lean-optrates -- https://github.com/shiy1022/lean-optrates
  commit 4c0b84980914ea7f9007510d92bcd60e91ad8448
  file   Optrates/Stochastic/Accumulation.lean
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
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap



/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yueheng Shi
-/

/-!
# L3c — How errors accumulate in a recursive estimator

**The scientific content of the library.**  A recursive gradient estimator (SARAH, SPIDER,
STORM, and the variance-reduction family generally) has error obeying one recursion,

`e_{k+1} = e_k + ξ_k`,

and the whole question of whether such an estimator is worth building is: how does `‖e_k‖`
grow with `k`?  The answer depends *only* on which oracle supplies the increments `ξ_k`:

* **Bounded (deterministic) increments** — `‖ξ_k‖ ≤ δ` — accumulate **linearly**:
  `‖e_K‖ ≤ ‖e_0‖ + K δ`, and `accumulation_linear_tight` exhibits increments attaining it.
* **Unbiased increments** — orthogonal in `L²`, `E‖ξ_k‖² ≤ δ²` — accumulate as **√K**:
  `E‖e_K‖² ≤ E‖e_0‖² + K δ²`.

Same recursion, same `δ`, different oracle contract, and the exponent on `K` differs.
This is the fact that decides whether recursive variance reduction transfers to a
bounded-error (e.g. quantum) oracle, and it is exactly the kind of claim that should be
machine-checked rather than asserted: the linear bound is *tight*, so the loss is real and
not an artifact of a lossy proof.

## Main results

* `accumulation_linear` / `accumulation_linear_tight` — the deterministic law, and its
  tightness witness.
* `accumulation_sq` — the `L²` law under orthogonal increments.
* `separation_linear_vs_sqrt` — the two laws side by side, with the crossover.
-/

section
open ShiOptRates
open ShiOptRates.Stochastic

open MeasureTheory Finset
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Bounded increments accumulate linearly -/

/-! ### Unbiased increments accumulate as `√K`

The hypothesis `horth` — that each increment is orthogonal in `L²` to the accumulated error
before it — is precisely what a martingale-difference sequence provides.  See
`Optrates.Stochastic.Bridge` for the derivation of `horth` from a conditional-expectation
hypothesis. -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable [CompleteSpace E]

omit [IsProbabilityMeasure μ] [CompleteSpace E] in

theorem solution {e ξ : ℕ → Ω → E} {δ : ℝ} (K : ℕ)
    (hrec : ∀ k ω, e (k + 1) ω = e k ω + ξ k ω)
    (hein : ∀ k, Integrable (fun ω => ‖e k ω‖ ^ 2) μ)
    (hxin : ∀ k, Integrable (fun ω => ‖ξ k ω‖ ^ 2) μ)
    (hcin : ∀ k, Integrable (fun ω => ⟪e k ω, ξ k ω⟫_ℝ) μ)
    (horth : ∀ k, ∫ ω, ⟪e k ω, ξ k ω⟫_ℝ ∂μ = 0)
    (hbnd : ∀ k, ∫ ω, ‖ξ k ω‖ ^ 2 ∂μ ≤ δ ^ 2) :
    ∫ ω, ‖e K ω‖ ^ 2 ∂μ ≤ (∫ ω, ‖e 0 ω‖ ^ 2 ∂μ) + K * δ ^ 2 := by
  induction K with
  | zero => simp
  | succ n ih =>
      -- expand the squared norm of the recursion, pointwise
      have hpt : ∀ ω, ‖e (n + 1) ω‖ ^ 2
          = ‖e n ω‖ ^ 2 + 2 * ⟪e n ω, ξ n ω⟫_ℝ + ‖ξ n ω‖ ^ 2 := by
        intro ω; rw [hrec n ω, norm_add_sq_real]
      have hc2 : Integrable (fun ω => 2 * ⟪e n ω, ξ n ω⟫_ℝ) μ := by
        exact (hcin n).const_mul 2
      have hsum1 : Integrable (fun ω => ‖e n ω‖ ^ 2 + 2 * ⟪e n ω, ξ n ω⟫_ℝ) μ := by
        exact (hein n).add hc2
      have hsplit : ∫ ω, ‖e (n + 1) ω‖ ^ 2 ∂μ
          = ∫ ω, ‖e n ω‖ ^ 2 ∂μ + 2 * ∫ ω, ⟪e n ω, ξ n ω⟫_ℝ ∂μ
            + ∫ ω, ‖ξ n ω‖ ^ 2 ∂μ := by
        rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
          integral_add hsum1 (hxin n), integral_add (hein n) hc2, integral_const_mul]
      rw [hsplit, horth n]
      push_cast
      have := hbnd n
      linarith [ih]

end
