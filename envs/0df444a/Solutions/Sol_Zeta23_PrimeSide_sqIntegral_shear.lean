-- Prove2me | solution 1 for Zeta23.PrimeSide.sqIntegral_shear
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T06:23:25.37355+00:00
-- url     : https://prove2.me/submissions/1370462e-4ae8-402b-afb5-3abe249123b1

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


lemma measurePreserving_shear :
    MeasurePreserving (fun z : ℝ × ℝ => (z.1 + z.2, z.2)) volume volume := by
  have := measurePreserving_add_prod (volume : Measure ℝ) (volume : Measure ℝ)
  rwa [← Measure.volume_eq_prod] at this


lemma measurableSet_Ix (T x : ℝ) : MeasurableSet (Ix T x) := by
  unfold Ix; exact measurableSet_Icc

lemma mem_Ix {T x τ' : ℝ} : τ' ∈ Ix T x ↔ x + τ' ∈ Icc T (2 * T) ∧ τ' ∈ Icc T (2 * T) := by
  simp only [Ix, Set.mem_Icc, max_le_iff, le_min_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, h2, h4⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, h3⟩, by linarith, h4⟩






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
variable {Φ : ℝ → ℝ} {T : ℝ}

theorem solution (hΦ : Continuous Φ) {G : ℝ × ℝ → ℝ} (hG : Continuous G) :
    ∫ q in Icc T (2 * T) ×ˢ Icc T (2 * T), Φ (q.1 - q.2) ^ 2 * G q
      = ∫ x, Φ x ^ 2 * ∫ τ' in Ix T x, G (x + τ', τ') := by
  set S := Icc T (2 * T) with hS
  have hSm : MeasurableSet (S ×ˢ S) := measurableSet_Icc.prod measurableSet_Icc
  set f : ℝ × ℝ → ℝ := fun q => Φ (q.1 - q.2) ^ 2 * G q with hf
  have hfint : IntegrableOn f (S ×ˢ S) := by
    apply ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    apply Continuous.continuousOn; fun_prop
  have hind : Integrable ((S ×ˢ S).indicator f) := (integrable_indicator_iff hSm).mpr hfint
  have hemb : MeasurableEmbedding (fun z : ℝ × ℝ => (z.1 + z.2, z.2)) :=
    shearHomeo.measurableEmbedding
  have hcomp : Integrable (fun z : ℝ × ℝ => (S ×ˢ S).indicator f (z.1 + z.2, z.2))
      (volume.prod volume) := by
    have := (measurePreserving_shear.integrable_comp_emb hemb).mpr hind
    rwa [Measure.volume_eq_prod] at this
  -- pointwise identification of the sheared integrand
  have hpt : ∀ x τ', (S ×ˢ S).indicator f (x + τ', τ')
      = (Ix T x).indicator (fun τ' => Φ x ^ 2 * G (x + τ', τ')) τ' := by
    intro x τ'
    by_cases h : τ' ∈ Ix T x
    · have h' : (x + τ', τ') ∈ S ×ˢ S := Set.mk_mem_prod (mem_Ix.mp h).1 (mem_Ix.mp h).2
      rw [Set.indicator_of_mem h', Set.indicator_of_mem h, hf]
      simp
    · have h' : (x + τ', τ') ∉ S ×ˢ S := fun hh => h (mem_Ix.mpr ⟨hh.1, hh.2⟩)
      rw [Set.indicator_of_notMem h', Set.indicator_of_notMem h]
  calc ∫ q in S ×ˢ S, f q
      = ∫ q, (S ×ˢ S).indicator f q := (integral_indicator hSm).symm
    _ = ∫ z : ℝ × ℝ, (S ×ˢ S).indicator f (z.1 + z.2, z.2) :=
        (measurePreserving_shear.integral_comp hemb _).symm
    _ = ∫ x, ∫ τ', (S ×ˢ S).indicator f (x + τ', τ') := by
        rw [Measure.volume_eq_prod, integral_prod _ hcomp]
    _ = ∫ x, Φ x ^ 2 * ∫ τ' in Ix T x, G (x + τ', τ') := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
        simp_rw [hpt x]
        rw [integral_indicator (measurableSet_Ix T x), integral_const_mul]
