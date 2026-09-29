-- Prove2me | solution 1 for Zeta23.PrimeSide.MV_primeRange
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T06:30:28.761917+00:00
-- url     : https://prove2.me/submissions/a8d30327-7fe1-4298-a071-2e7ee94126b1

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
import Theorems.Thm_Zeta23_PrimeSide_inv_two_mul_le_abs_log_sub

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

lemma one_le_of_mem_primeRange {X : ℝ} {n : ℕ} (hn : n ∈ primeRange X) : 1 ≤ n :=
  (Finset.mem_Ioc.mp hn).1










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

theorem solution (hMV : Zeta23.MVHilbert C) (X : ℝ) (x z : ℕ → ℂ) :
    ‖∑ n ∈ primeRange X, ∑ m ∈ primeRange X,
        (if n = m then (0:ℂ) else x n * conj (z m) / ((Real.log n - Real.log m : ℝ) : ℂ))‖
      ≤ C * Real.sqrt (∑ n ∈ primeRange X, ‖x n‖ ^ 2 * (2 * n))
          * Real.sqrt (∑ n ∈ primeRange X, ‖z n‖ ^ 2 * (2 * n)) := by
  set S := primeRange X with hS
  have key := hMV S (fun r : S => Real.log ((r:ℕ):ℝ)) (fun r : S => 1 / (2 * ((r:ℕ):ℝ)))
    (fun r => x r) (fun r => z r) ?_ ?_ ?_
  · have e1 : (∑ r : S, ∑ s : S, if r = s then (0:ℂ) else
        x r * conj (z s) / ((Real.log ((r:ℕ):ℝ) - Real.log ((s:ℕ):ℝ) : ℝ) : ℂ))
        = ∑ n ∈ S, ∑ m ∈ S, (if n = m then (0:ℂ) else
            x n * conj (z m) / ((Real.log n - Real.log m : ℝ) : ℂ)) := by
      simp_rw [Subtype.ext_iff]
      rw [Finset.sum_coe_sort S (fun n => ∑ s : S, if n = (s:ℕ) then (0:ℂ) else
            x n * conj (z s) / ((Real.log n - Real.log ((s:ℕ):ℝ) : ℝ) : ℂ))]
      refine Finset.sum_congr rfl fun n _ => ?_
      exact Finset.sum_coe_sort S (fun m => if n = m then (0:ℂ) else
            x n * conj (z m) / ((Real.log n - Real.log m : ℝ) : ℂ))
    have e2 : ∀ (w : ℕ → ℂ), (∑ r : S, ‖w r‖ ^ 2 / (1 / (2 * ((r:ℕ):ℝ))))
        = ∑ n ∈ S, ‖w n‖ ^ 2 * (2 * n) := by
      intro w
      rw [Finset.sum_coe_sort S (fun n => ‖w n‖ ^ 2 / (1 / (2 * (n:ℝ))))]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [div_div_eq_mul_div, div_one]
    rw [e1, e2 x, e2 z] at key
    exact key
  · intro r s hrs
    apply Subtype.ext
    have hr : (0:ℝ) < ((r:ℕ):ℝ) := by exact_mod_cast one_le_of_mem_primeRange r.2
    have hs : (0:ℝ) < ((s:ℕ):ℝ) := by exact_mod_cast one_le_of_mem_primeRange s.2
    have : ((r:ℕ):ℝ) = ((s:ℕ):ℝ) := Real.log_injOn_pos (Set.mem_Ioi.mpr hr) (Set.mem_Ioi.mpr hs) hrs
    exact_mod_cast this
  · intro r
    have hr : (0:ℝ) < ((r:ℕ):ℝ) := by exact_mod_cast one_le_of_mem_primeRange r.2
    positivity
  · intro r s hrs
    exact inv_two_mul_le_abs_log_sub (one_le_of_mem_primeRange r.2)
      (one_le_of_mem_primeRange s.2) (fun h => hrs (Subtype.ext h))
