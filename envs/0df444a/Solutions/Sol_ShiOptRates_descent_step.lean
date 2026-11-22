-- Prove2me | solution 1 for ShiOptRates.descent_step
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-08T22:46:44.021534+00:00
-- url     : https://prove2.me/submissions/c7dd89be-a1d8-4d21-b136-f995af2153f8

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

theorem solution (hL : 0 < L) (hQ : QuadUpper f g L) (x gd : E) :
    ‖g x‖ ^ 2 ≤ 2 * L * (f x - f (x - L⁻¹ • gd)) + ‖gd - g x‖ ^ 2 := by
  set y : E := x - L⁻¹ • gd with hy
  set e : E := gd - g x with he
  have hgd : gd = g x + e := by rw [he]; abel
  have hyx : y - x = -(L⁻¹ • gd) := by rw [hy]; abel
  have hinner : ⟪g x, y - x⟫_ℝ = -(L⁻¹ * ⟪g x, gd⟫_ℝ) := by
    rw [hyx, inner_neg_right, real_inner_smul_right]
  have hnorm : ‖y - x‖ ^ 2 = (L⁻¹) ^ 2 * ‖gd‖ ^ 2 := by
    rw [hyx, norm_neg, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  -- the two identities that make the cross terms cancel
  have hA : ⟪g x, gd⟫_ℝ = ‖g x‖ ^ 2 + ⟪g x, e⟫_ℝ := by
    rw [hgd, inner_add_right, real_inner_self_eq_norm_sq]
  have hB : ‖gd‖ ^ 2 = ‖g x‖ ^ 2 + 2 * ⟪g x, e⟫_ℝ + ‖e‖ ^ 2 := by
    rw [hgd, norm_add_sq_real]
  have hstep := hQ x y
  rw [hinner, hnorm] at hstep
  -- clear the `1/L`s
  have hLne : L ≠ 0 := ne_of_gt hL
  have hkey : 2 * L * (f y - f x) ≤ -‖g x‖ ^ 2 + ‖e‖ ^ 2 := by
    have h2L : (0 : ℝ) < 2 * L := by linarith
    have hmul := mul_le_mul_of_nonneg_left hstep (le_of_lt h2L)
    have hid : 2 * L * (f x + -(L⁻¹ * ⟪g x, gd⟫_ℝ) + L / 2 * ((L⁻¹) ^ 2 * ‖gd‖ ^ 2))
        = 2 * L * f x - 2 * ⟪g x, gd⟫_ℝ + ‖gd‖ ^ 2 := by
      field_simp
      ring
    rw [hid] at hmul
    rw [hA, hB] at hmul
    nlinarith [hmul]
  nlinarith [hkey]

end
