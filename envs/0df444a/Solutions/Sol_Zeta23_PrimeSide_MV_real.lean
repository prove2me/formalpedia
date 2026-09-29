-- Prove2me | solution 1 for Zeta23.PrimeSide.MV_real
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T06:28:51.578797+00:00
-- url     : https://prove2.me/submissions/fd7a5da1-d827-47c2-bf96-7c82119174ac

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Defs
import Definitions.Def_Zeta23_PrimeSideB_PPKernel
import Theorems.Thm_Zeta23_PrimeSide_MV_primeRange

-- from Zeta23.PrimeSideB.PPKernel
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization of the paper
"More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/

/-!
# Kernel lemmas for [prop:PP] (§5.4)

Pure measure-theory / trigonometric-integral / H-MV-application lemmas used by
`Zeta23/PrimeSideB/PP.lean`.

* `sqIntegral_shear`: the substitution `τ = τ' + x` on the square `I×I` (§5.4).
* `intervalIntegral_cos_linear*`: `∫_α^β cos(θt + c) dt` closed forms and the bound `2/|θ|` (§5.4).
-/

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction ComplexConjugate

namespace Zeta23
namespace PrimeSide

/-! ## Elementary facts about the index range `primeRange X = Finset.Ioc 0 ⌊X⌋₊` -/

section Basics











end Basics

/-! ## The shear `(τ,τ') ↦ (x,τ') = (τ−τ',τ')` on `I × I`  (§5.4) -/

section Shear
variable {Φ : ℝ → ℝ} {T : ℝ}











end Shear

/-! ## The inner `τ'`-integrals:  `∫_α^β cos(θt + c) dt`  (§5.4) -/

section CosIntegral









variable {T : ℝ}


end CosIntegral

/-! ## Per-frequency-pair decomposition of `𝓜[cos(·y), cos(·y')]`  ([eq:MPP], §5.4) -/

section PairDecomp
variable {Φ : ℝ → ℝ} {T : ℝ}






/-! ### The diagonal 𝒟 (§5.4) -/



/-! ### The sum-frequency terms 𝒪₂ (§5.4) -/


/-! ### The difference-frequency terms 𝒪₁, exact evaluation (§5.4) -/






end PairDecomp

/-! ## Applying H-MV on the prime-power frequencies  ([lem:MV], [eq:deltan]; §5.1, §5.4) -/

section MVapply
variable {C : ℝ}





end MVapply

end PrimeSide
end Zeta23
end
open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction ComplexConjugate
open Zeta23
open PrimeSide
variable {C : ℝ}

theorem solution (hMV : Zeta23.MVHilbert C) (X c : ℝ) (u v : ℕ → ℝ) :
    |∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
        u n * v m * Real.cos (c * (Real.log n - Real.log m)) / (Real.log n - Real.log m))|
      ≤ C * Real.sqrt (∑ n ∈ primeRange X, u n ^ 2 * (2 * n))
          * Real.sqrt (∑ n ∈ primeRange X, v n ^ 2 * (2 * n)) ∧
    |∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
        u n * v m * Real.sin (c * (Real.log n - Real.log m)) / (Real.log n - Real.log m))|
      ≤ C * Real.sqrt (∑ n ∈ primeRange X, u n ^ 2 * (2 * n))
          * Real.sqrt (∑ n ∈ primeRange X, v n ^ 2 * (2 * n)) := by
  set x : ℕ → ℂ := fun n => (u n : ℂ) * Complex.exp ((c * Real.log n : ℝ) * Complex.I) with hx
  set z : ℕ → ℂ := fun n => (v n : ℂ) * Complex.exp ((c * Real.log n : ℝ) * Complex.I) with hz
  have key := MV_primeRange hMV X x z
  have hnx : ∀ n, ‖x n‖ ^ 2 = u n ^ 2 := by
    intro n
    simp only [hx, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  have hnz : ∀ n, ‖z n‖ ^ 2 = v n ^ 2 := by
    intro n
    simp only [hz, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  simp_rw [hnx, hnz] at key
  have hprod : ∀ n m, x n * conj (z m)
      = ((u n * v m : ℝ) : ℂ) * Complex.exp ((c * (Real.log n - Real.log m) : ℝ) * Complex.I) := by
    intro n m
    have harg : ((c * Real.log n : ℝ) : ℂ) * Complex.I
        + ((c * Real.log m : ℝ) : ℂ) * (starRingEnd ℂ) Complex.I
        = ((c * (Real.log n - Real.log m) : ℝ) : ℂ) * Complex.I := by
      rw [Complex.conj_I]; push_cast; ring
    simp only [hx, hz, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    rw [mul_mul_mul_comm, ← Complex.exp_add, harg]
    push_cast; ring
  have hre : (∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
        (if n = m then (0:ℂ) else x n * conj (z m) / ((Real.log n - Real.log m : ℝ) : ℂ))).re
      = ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
        u n * v m * Real.cos (c * (Real.log n - Real.log m)) / (Real.log n - Real.log m)) := by
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs with h
    · simp
    · rw [hprod, Complex.div_ofReal_re, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]
  have him : (∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
        (if n = m then (0:ℂ) else x n * conj (z m) / ((Real.log n - Real.log m : ℝ) : ℂ))).im
      = ∑ n ∈ primeRange X, ∑ m ∈ primeRange X, (if n = m then (0:ℝ) else
        u n * v m * Real.sin (c * (Real.log n - Real.log m)) / (Real.log n - Real.log m)) := by
    rw [Complex.im_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.im_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs with h
    · simp
    · rw [hprod, Complex.div_ofReal_im, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  constructor
  · rw [← hre]; exact (Complex.abs_re_le_norm _).trans key
  · rw [← him]; exact (Complex.abs_im_le_norm _).trans key
