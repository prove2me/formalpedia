-- Prove2me | solution 1 for Zeta23.Cheb.chebyshevMertens
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T08:09:11.623495+00:00
-- url     : https://prove2.me/submissions/d1b9b45e-1064-47cf-ae32-37c480b07656

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Mertens
import Definitions.Def_Zeta23_Hypotheses
import Theorems.Thm_Zeta23_Cheb_sum_vonMangoldt_div_sqrt_le_three_explicit
import Theorems.Thm_Zeta23_Cheb_sum_vonMangoldt_div_sqrt_mul_log_le
import Theorems.Thm_Zeta23_Cheb_sum_vonMangoldt_sq_div_eq_explicit
import Theorems.Thm_Zeta23_Cheb_sum_vonMangoldt_sq_div_mul_log_sub_eq_explicit
import Theorems.Thm_Zeta23_Cheb_sum_vonMangoldt_sq_le

-- from Zeta23.Chebyshev
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Chebyshev.lean — discharge of the Chebyshev-type hypothesis H-cheb.

Paper: "More than two thirds of the zeros of the Riemann zeta function lie on
the critical line", Lemma [lem:cheb], displays [eq:cheb1]–[eq:cheb2]:

  "For x ≥ 2,
     Σ_{n≤x} Λ(n) ≪ x,   Σ_{n≤x} Λ(n)/√n ≤ 3√x  (x ≥ x₀),
     Σ_{n≤x} Λ(n)/(√n log n) ≪ √x/log x,   Σ_{n≤x} Λ(n)² ≪ x log x,    [eq:cheb1]
     Σ_{n≤x} Λ(n)²/n = (log x)²/2 + O(log x),
     Σ_{n≤x} Λ(n)²/n (log x − log n) = (log x)³/6 + O((log x)²).       [eq:cheb2]"

H-cheb is classical [MV07 §2.2].  All sums here run over n ∈ Finset.Ioc 0 ⌊x⌋₊,
matching Mathlib's `Chebyshev.psi`.  The ≪-bounds are stated with explicit
existential constants; the paper's "≤ 3√x eventually" is provided in the robust
∃-constant form (the constant is not load-bearing downstream — [eq:Bdef] only
needs *some* B = l + C√X).

The two [eq:cheb2] asymptotics need Mertens' first theorem
Σ_{n≤x} Λ(n)/n = log x + O(1), which is not in Mathlib; it is supplied by
`mertensFirst` below, via Zeta23/FromPNTPlus/Mertens.lean.

Everything else comes from Mathlib (NumberTheory.Chebyshev ψ-bounds +
elementary induction/splitting arguments).
-/

namespace Zeta23
namespace Cheb

open Finset Real Chebyshev
open ArithmeticFunction hiding log
open scoped Nat.Prime

/-! ## [eq:cheb1], first bound: Σ_{n≤x} Λ(n) ≪ x -/

/-- [eq:cheb1].1: Σ_{n≤x} Λ(n) ≪ x, with Mathlib's explicit Chebyshev constant. -/
theorem sum_vonMangoldt_le {x : ℝ} (hx : 0 ≤ x) :
    ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ≤ (Real.log 4 + 4) * x :=
  Chebyshev.psi_le_const_mul_self hx

/-! ## [eq:cheb1], second bound: Σ_{n≤x} Λ(n)/√n ≪ √x -/


section Cheb1b

open MeasureTheory intervalIntegral





end Cheb1b




/-- [eq:cheb1].2, the paper's literal form (∃-version; witness = the explicit threshold above). -/
theorem sum_vonMangoldt_div_sqrt_le_three :
    ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n / Real.sqrt n ≤ 3 * Real.sqrt x :=
  ⟨max 1 ((48 / (3 - 2 * Real.log 4)) ^ 4), fun _ hx => sum_vonMangoldt_div_sqrt_le_three_explicit hx⟩

/-! ## [eq:cheb1], third bound: Σ_{n≤x} Λ(n)/(√n log n) ≪ √x/log x -/



/-! ## [eq:cheb1], fourth bound: Σ_{n≤x} Λ(n)² ≪ x log x -/



/-! ## [eq:cheb2]: the two Mertens-type asymptotics

Mertens' first theorem Σ_{n≤x} Λ(n)/n = log x + O(1) is supplied by
`Mertens.sum_mangoldt_div_eq_log` (see
Zeta23/FromPNTPlus/Mertens.lean), so both [eq:cheb2] bounds are unconditional. -/

section Cheb2

open MeasureTheory

















/-! ### The proper-prime-power defect

[lem:cheb] proof: "Σ_{n≤x} Λ(n)²/n = Σ_{n≤x} Λ(n) log n/n + O(1) (the two differ
only at proper prime powers)".  The defect Σ_{n≤x} Λ(n)(log n − Λ(n))/n is
supported on prime powers pᵏ with k ≥ 2, where its value is (k−1)log²p/pᵏ;
summing over all p, k bounds it by an absolute constant. -/











/-- [eq:cheb2].1: Σ_{n≤x} Λ(n)²/n = (log x)²/2 + O(log x).
Paper [lem:cheb]: "Σ_{n≤x} Λ(n)²/n = Σ_{n≤x} Λ(n) log n/n + O(1) ..., and partial
summation from Mertens' formula gives Σ_{n≤x} Λ(n) log n/n = ½log²x + O(log x)."
(From the explicit-constant version.) -/
theorem sum_vonMangoldt_sq_div_eq :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |(∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n) - Real.log x ^ 2 / 2| ≤ C * Real.log x := by
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hlog4pos : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  exact ⟨_, by positivity, sum_vonMangoldt_sq_div_eq_explicit⟩


/-- [eq:cheb2].2: Σ_{n≤x} (Λ(n)²/n)(log x − log n) = (log x)³/6 + O((log x)²).
Paper [lem:cheb]: "The second formula is ∫₁ˣ (Σ_{n≤t} Λ(n)²/n) dt/t."  (From the explicit-constant version.) -/
theorem sum_vonMangoldt_sq_div_mul_log_sub_eq :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 2 ≤ x →
      |(∑ n ∈ Ioc 0 ⌊x⌋₊, Λ n ^ 2 / n * (Real.log x - Real.log n)) -
          Real.log x ^ 3 / 6| ≤ C * Real.log x ^ 2 := by
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hlog4pos : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  exact ⟨_, by positivity, sum_vonMangoldt_sq_div_mul_log_sub_eq_explicit⟩


end Cheb2

end Cheb
end Zeta23
open Zeta23
open Cheb
open Finset Real Chebyshev
open ArithmeticFunction hiding log
open scoped Nat.Prime
open MeasureTheory

theorem solution : ChebyshevMertens where
  cheb1a := ⟨Real.log 4 + 4, fun x hx => sum_vonMangoldt_le (by linarith)⟩
  cheb1b := sum_vonMangoldt_div_sqrt_le_three
  cheb1c := ⟨4 * Real.log 4 + 40, fun x hx => sum_vonMangoldt_div_sqrt_mul_log_le hx⟩
  cheb1d := ⟨Real.log 4 + 4, fun x hx => sum_vonMangoldt_sq_le (by linarith)⟩
  cheb2a := by
    obtain ⟨C, _, h⟩ := sum_vonMangoldt_sq_div_eq
    exact ⟨C, fun x hx => h x hx⟩
  cheb2b := by
    obtain ⟨C, _, h⟩ := sum_vonMangoldt_sq_div_mul_log_sub_eq
    exact ⟨C, fun x hx => h x hx⟩
