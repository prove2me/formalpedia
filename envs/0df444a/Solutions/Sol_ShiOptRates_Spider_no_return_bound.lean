-- Prove2me | solution 1 for ShiOptRates.Spider.no_return_bound
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-08T22:59:22.625469+00:00
-- url     : https://prove2.me/submissions/0ca30f5b-8769-49ce-a41f-b58a125d0cb6

/-
Derived from lean-optrates -- https://github.com/shiy1022/lean-optrates
  commit 4c0b84980914ea7f9007510d92bcd60e91ad8448
  file   Optrates/Spider.lean
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
import Definitions.Def_ShiOptrates_Spider
import Definitions.Def_ShiOptrates_Stochastic_Bridge
import Definitions.Def_ShiOptrates_Stochastic_Recursion
import Definitions.Def_ShiOptrates_Stochastic_VariancePurchase
import Theorems.Thm_ShiOptRates_Spider_step_decrease
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Probability.Martingale.Basic



/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yueheng Shi
-/

/-!
# L4 / GL4 — SPIDER and Q-SPIDER

The recursive variance-reduction rate, at both cost exponents.

SPIDER (Fang et al. 2018) refreshes a full gradient estimate every `q` steps and, in
between, updates it by an estimate of the *increment* `∇f(xₜ) - ∇f(xₜ₋₁)`.  Under mean-
squared smoothness the increment is small — its variance is at most `ℓ²‖xₜ - xₜ₋₁‖²` — so
it can be estimated cheaply, and the accumulated error over an epoch is controlled by
`Stochastic.accumulation_sq`.

Q-SPIDER (Sidford–Zhang, arXiv:2308.01582, Algorithm 7) is the *same algorithm with the
same schedule*, with the classical variance-reduction step replaced by their quantum
variance reduction (their Theorem 4), which delivers an **unbiased** estimate of variance
`σ̂²` at price `√d · scale / σ̂` instead of the classical `scale² / σ̂²`.

So the two published rates, `ε⁻³` and `√d ε⁻⁵ᐟ²`, are the *same schedule* priced at two
cost exponents.  That is what `spider_queries_classical` and `spider_queries_quantum`
below establish, in closed form with explicit constants.

## Main definitions

* `MeanSquaredSmooth` — `E‖G x ω - G y ω‖² ≤ ℓ²‖x - y‖²`, the function class SPIDER needs.
* `mePrice scale σhat p a` — `a · (scale/σhat)^p`: mean-estimation price, classical at
  `p = 2, a = 1` and quantum at `p = 1, a = √d`.
* `spiderTotal` — the query bill of Algorithm 7's schedule at a given exponent.

## Main results

* `increment_variance_le` — the increment-variance bound, and `increment_variance_le_sq`
  its specialization at the algorithm's normalized step `ε/ℓ`.
* `epoch_error_le` — the accumulated epoch error, via `accumulation_sq`.
* `schedule_budget` — **the schedule verification**: Algorithm 7's `(q, σ̂₁, σ̂₂)` spend
  exactly `3ε²/1600` of error budget, so the claimed accuracy holds with slack.
* `spider_queries_classical` — `≍ 2.56·10⁷ · ℓ Δ σ / ε³`.
* `spider_queries_quantum` — `≍ 6.4·10⁴ √10 · ℓ Δ √(dσ) / ε⁵ᐟ²`.
* `quantum_beats_classical_iff` — the crossover: the quantum bill is smaller exactly when
  `d ε < 16000 σ`.  The dimension-versus-accuracy tradeoff, with the constant.

## What this file does and does not establish

It reproduces the **query complexity** of both algorithms, with explicit constants, and the
epoch error control that makes the schedule valid.  It does *not* prove that Algorithm 7's
output is an `ε`-critical point: that is Fang et al.'s Theorem 1, which Sidford–Zhang also
import rather than reprove (their Theorem 9).  The formalization therefore mirrors the
structure of the published proof exactly — correctness cited, query count computed — and
the correctness half remains open.  Closing it means formalizing SPIDER's descent argument
under the normalized step and the `‖vₜ‖ ≤ 2ε` early return.
-/

section
open ShiOptRates
open ShiOptRates.Spider

open MeasureTheory Finset
open scoped InnerProductSpace

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The function class -/

/-! ### The epoch error, via the accumulation law -/

variable [IsProbabilityMeasure μ] [CompleteSpace E]

end

/-! ### The schedule and the query bill

From here everything is arithmetic on Algorithm 7's stated parameters:

`q = 20σ/ε`, `σ̂₁ = ε/40`, `σ̂₂ = (ε/40)·√(ε/(10σ))`, budget `𝒯 = 1600 ℓΔ/ε²`.
-/

section
open ShiOptRates
open ShiOptRates.Spider

/-! ### The correctness half: the algorithm cannot run forever without returning

Algorithm 7 takes a *normalized* step of length `ε/ℓ` in the direction `-vₜ/‖vₜ‖`, and
returns `xₜ` as soon as `‖vₜ‖ ≤ 2ε`.  The content of correctness is that it must return
soon: while `‖vₜ‖ > 2ε` and the estimate is `ε`-accurate, every step buys `ε²/(2ℓ)` of
objective decrease, so at most `2ℓΔ₀/ε²` such steps can occur.

Everything here is deterministic, conditioned on the accuracy event `‖vₜ - ∇f(xₜ)‖ ≤ ε`;
`epoch_error_le` is what makes that event likely.  The remaining gap to Fang et al.'s
Theorem 1 is the probabilistic wrapper — bounding `E‖e_τ‖` at the *random* return time `τ`,
where conditioning on `τ = k` breaks the unconditional variance bound.  That step, and only
that step, is still open. -/

section Correctness

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → ℝ} {g : E → E} {ℓ ε : ℝ}

theorem solution (hQ : QuadUpper f g ℓ) (hℓ : 0 < ℓ) (hε : 0 < ε) {fstar : ℝ}
    (x v : ℕ → E) (T : ℕ) (hlow : fstar ≤ f (x T))
    (hstep : ∀ t < T, x (t + 1) = x t - (ε / ℓ) • (‖v t‖⁻¹ • v t))
    (herr : ∀ t < T, ‖v t - g (x t)‖ ≤ ε)
    (hbig : ∀ t < T, 2 * ε < ‖v t‖) :
    (T : ℝ) ≤ 2 * ℓ * (f (x 0) - fstar) / ε ^ 2 := by
  have hdec : ∀ t ∈ Finset.range T, f (x (t + 1)) - f (x t) ≤ -(ε ^ 2 / (2 * ℓ)) := by
    intro t ht
    have ht' : t < T := Finset.mem_range.mp ht
    have h := step_decrease hQ hℓ hε (herr t ht') (hbig t ht')
    rw [← hstep t ht'] at h
    linarith
  have hsum : ∑ t ∈ Finset.range T, (f (x (t + 1)) - f (x t))
      ≤ ∑ _t ∈ Finset.range T, (-(ε ^ 2 / (2 * ℓ))) := Finset.sum_le_sum hdec
  rw [Finset.sum_range_sub (fun t => f (x t)) T, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hsum
  have hstep2 : (T : ℝ) * (ε ^ 2 / (2 * ℓ)) ≤ f (x 0) - fstar := by nlinarith [hsum, hlow]
  rw [le_div_iff₀ (by positivity : (0:ℝ) < ε ^ 2)]
  have h2 := mul_le_mul_of_nonneg_left hstep2 (by positivity : (0:ℝ) ≤ 2 * ℓ)
  have hid2 : 2 * ℓ * ((T : ℝ) * (ε ^ 2 / (2 * ℓ))) = (T : ℝ) * ε ^ 2 := by
    field_simp
  rw [hid2] at h2
  linarith [h2]

end Correctness

end
