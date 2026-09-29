-- Prove2me | solution 1 for Zeta23.PrimeSide.inner_cos_cos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T06:25:13.351631+00:00
-- url     : https://prove2.me/submissions/58bcf714-b176-4f65-bf7e-cc6cb3eece54

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









/-- On `|x| ≤ T` (and `T ≥ 0`) the window is the honest interval `[max(T−x,T), min(2T−x,2T)]`
with left end ≤ right end, of length `T − |x|`. -/
lemma Ix_le (hT : 0 ≤ T) {x : ℝ} (hx : |x| ≤ T) :
    max (T - x) T ≤ min (2 * T - x) (2 * T) := by
  rw [abs_le] at hx
  simp only [max_le_iff, le_min_iff]; refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩


end Shear

/-! ## The inner `τ'`-integrals:  `∫_α^β cos(θt + c) dt`  (§5.4) -/

section CosIntegral

/-- `cos A cos B = (cos(A−B) + cos(A+B))/2` (§5.4, real form of
`P_X(τ)P_X(τ') = (1/2π²) Re Σ a_n a_m [n^{iτ}m^{−iτ'} + n^{iτ}m^{iτ'}]`). -/
lemma cos_mul_cos_eq (A B : ℝ) :
    Real.cos A * Real.cos B = (Real.cos (A - B) + Real.cos (A + B)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]; ring


lemma intervalIntegral_cos_linear {θ : ℝ} (hθ : θ ≠ 0) (c α β : ℝ) :
    ∫ t in α..β, Real.cos (θ * t + c) = (Real.sin (θ * β + c) - Real.sin (θ * α + c)) / θ := by
  rw [intervalIntegral.integral_comp_mul_add (fun t => Real.cos t) hθ c, integral_cos,
    smul_eq_mul, inv_mul_eq_div]

lemma intervalIntegral_cos_linear_eq_Jker (θ c α β : ℝ) :
    ∫ t in α..β, Real.cos (θ * t + c) = Jker θ c α β := by
  unfold Jker
  split_ifs with hθ
  · subst hθ; simp [intervalIntegral.integral_const]
  · exact intervalIntegral_cos_linear hθ c α β





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
variable {T : ℝ}

theorem solution (hT : 0 ≤ T) {x : ℝ} (hx : |x| ≤ T) (y y' : ℝ) :
    ∫ τ' in Ix T x, Real.cos ((x + τ') * y) * Real.cos (τ' * y')
      = (Jker (y - y') (x * y) (max (T - x) T) (min (2 * T - x) (2 * T))
          + Jker (y + y') (x * y) (max (T - x) T) (min (2 * T - x) (2 * T))) / 2 := by
  have hle := Ix_le hT hx
  unfold Ix
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle,
    ← intervalIntegral_cos_linear_eq_Jker, ← intervalIntegral_cos_linear_eq_Jker,
    ← intervalIntegral.integral_add (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop),
    ← intervalIntegral.integral_div]
  apply intervalIntegral.integral_congr
  intro t _
  simp only
  rw [cos_mul_cos_eq]
  congr 2 <;> (congr 1; ring)
