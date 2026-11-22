-- Prove2me | solution 1 for ShiOptRates.exists_grad_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-08T23:02:02.590683+00:00
-- url     : https://prove2.me/submissions/852602a3-e3f0-4c7a-af25-c3c141188d91

/-
Derived from lean-optrates -- https://github.com/shiy1022/lean-optrates
  commit 4c0b84980914ea7f9007510d92bcd60e91ad8448
  file   Optrates/Deterministic.lean
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
import Theorems.Thm_ShiOptRates_telescope
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
# L1 — Deterministic core

Inexact gradient descent on an `L`-smooth, lower-bounded objective, driven by an oracle
whose error is *deterministically* bounded by a per-iteration accuracy `δ k`.  There is no
probability anywhere in this file: no filtration, no conditional expectation, no
martingale.  That is the point — a quantum mean estimator's guarantee, conditioned on not
failing, is deterministic, so the quantum rate needs only this layer plus a union bound
(`Optrates.Failure`).

All constants are explicit.

## Main results

* `descent_step` — one step at stepsize `1/L`:
  `‖g x‖² ≤ 2L (f x - f x⁺) + ‖gᵈ - g x‖²`.
  The oracle error enters *additively and squared*, with constant `1`; the cross terms
  cancel exactly, so no Cauchy–Schwarz and no Young inequality is needed here.
* `telescope` — `∑_{k<K} ‖g xₖ‖² ≤ 2L (f x₀ - f x_K) + ∑_{k<K} δₖ²`.
* `exists_grad_sq_le` — the same bound divided by `K`, at some iterate.
* `exists_grad_le_of_const_schedule` — the ε-form: `δₖ² ≤ ε²/2` and `K ≥ 4LΔ₀/ε²` give an
  iterate with `‖g xₖ‖ ≤ ε`.
* `queries_of_const_schedule`, `queries_powerCost` — the query bill for that run,
  in closed form, as a function of the cost exponent.
-/

section
open ShiOptRates

open scoped InnerProductSpace
open Finset

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → ℝ} {g : E → E} {L : ℝ}

theorem solution (hL : 0 < L) (hQ : QuadUpper f g L) {fstar : ℝ}
    (x : ℕ → E) (gd : ℕ → E) (δ : ℕ → ℝ) (K : ℕ) (hK : 0 < K)
    (hlow : fstar ≤ f (x K))
    (hstep : ∀ k < K, x (k + 1) = x k - L⁻¹ • gd k)
    (herr : ∀ k < K, ‖gd k - g (x k)‖ ≤ δ k) :
    ∃ k < K, ‖g (x k)‖ ^ 2
      ≤ (2 * L * (f (x 0) - fstar) + ∑ j ∈ range K, (δ j) ^ 2) / K := by
  set S : ℝ := 2 * L * (f (x 0) - fstar) + ∑ j ∈ range K, (δ j) ^ 2 with hS
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have htel := telescope hL hQ x gd δ K hstep herr
  have hSle : ∑ k ∈ range K, ‖g (x k)‖ ^ 2 ≤ S := by
    have : 2 * L * (f (x 0) - f (x K)) ≤ 2 * L * (f (x 0) - fstar) := by
      have h2L : (0 : ℝ) ≤ 2 * L := by linarith
      have : f (x 0) - f (x K) ≤ f (x 0) - fstar := by linarith
      exact mul_le_mul_of_nonneg_left this h2L
    rw [hS]; linarith
  have hconst : ∑ _k ∈ range K, S / K = S := by
    rw [Finset.sum_const, card_range, nsmul_eq_mul]
    field_simp
  have hle : ∑ k ∈ range K, ‖g (x k)‖ ^ 2 ≤ ∑ _k ∈ range K, S / K := by
    rw [hconst]; exact hSle
  obtain ⟨k, hk, hklt⟩ :=
    Finset.exists_le_of_sum_le (nonempty_range_iff.mpr hK.ne') hle
  exact ⟨k, mem_range.mp hk, hklt⟩

end
