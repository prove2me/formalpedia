-- Prove2me | solution 1 for Zeta23.PrimeSide.abs_Aplus_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T06:10:03.711769+00:00
-- url     : https://prove2.me/submissions/f604a82e-b8a4-4679-bba1-0ab6d9ac6ff0

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











end Shear

/-! ## The inner `τ'`-integrals:  `∫_α^β cos(θt + c) dt`  (§5.4) -/

section CosIntegral






lemma Jker_of_ne {θ : ℝ} (hθ : θ ≠ 0) (c α β : ℝ) :
    Jker θ c α β = (Real.sin (θ * β + c) - Real.sin (θ * α + c)) / θ := by simp [Jker, hθ]

/-- `|J| ≤ 2/|θ|` for `θ ≠ 0` (§5.4 "≤ 2/log(nm)"). -/
lemma abs_Jker_le {θ : ℝ} (hθ : θ ≠ 0) (c α β : ℝ) : |Jker θ c α β| ≤ 2 / |θ| := by
  rw [Jker_of_ne hθ, abs_div]
  gcongr
  calc |Real.sin (θ * β + c) - Real.sin (θ * α + c)|
      ≤ |Real.sin (θ * β + c)| + |Real.sin (θ * α + c)| := abs_sub _ _
    _ ≤ 1 + 1 := add_le_add (Real.abs_sin_le_one _) (Real.abs_sin_le_one _)
    _ = 2 := by norm_num

/-- `J` as a function of the offset `x` (through `c = xy`, `α = max(T−x,T)`, `β = min(2T−x,2T)`)
is continuous. -/
lemma continuous_Jker_offset (θ y T : ℝ) :
    Continuous fun x : ℝ => Jker θ (x * y) (max (T - x) T) (min (2 * T - x) (2 * T)) := by
  by_cases hθ : θ = 0
  · simp only [Jker, hθ, if_true]; fun_prop
  · simp only [Jker, hθ, if_false]; fun_prop

variable {T : ℝ}


end CosIntegral

/-! ## Per-frequency-pair decomposition of `𝓜[cos(·y), cos(·y')]`  ([eq:MPP], §5.4) -/

section PairDecomp
variable {Φ : ℝ → ℝ} {T : ℝ}


lemma continuous_JpK (T y y' : ℝ) : Continuous (JpK T y y') := by
  unfold JpK; exact continuous_Jker_offset _ _ _




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
variable {Φ : ℝ → ℝ} {T : ℝ}

theorem solution (hΦ : Continuous Φ) (hΦ2 : Integrable fun x => Φ x ^ 2) {y y' : ℝ}
    (hyy : 0 < y + y') :
    |Aplus Φ T y y'| ≤ 2 / (y + y') * ∫ x, Φ x ^ 2 := by
  unfold Aplus
  have hne : y + y' ≠ 0 := hyy.ne'
  have hint : IntegrableOn (fun x => Φ x ^ 2 * JpK T y y' x) (Icc (-T) T) :=
    ((hΦ.pow 2).mul (continuous_JpK T y y')).integrableOn_Icc
  calc |∫ x in Icc (-T) T, Φ x ^ 2 * JpK T y y' x|
      ≤ ∫ x in Icc (-T) T, |Φ x ^ 2 * JpK T y y' x| := abs_integral_le_integral_abs
    _ ≤ ∫ x in Icc (-T) T, Φ x ^ 2 * (2 / (y + y')) := by
        apply setIntegral_mono_on hint.abs (hΦ2.integrableOn.mul_const _) measurableSet_Icc
        intro x _
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        have := abs_Jker_le hne (x * y) (max (T - x) T) (min (2 * T - x) (2 * T))
        rw [abs_of_pos hyy] at this
        exact this
    _ = 2 / (y + y') * ∫ x in Icc (-T) T, Φ x ^ 2 := by rw [integral_mul_const]; ring
    _ ≤ 2 / (y + y') * ∫ x, Φ x ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact setIntegral_le_integral hΦ2 (Filter.Eventually.of_forall fun x => sq_nonneg _)
