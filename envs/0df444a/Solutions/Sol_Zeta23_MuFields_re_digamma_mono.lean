-- Prove2me | solution 1 for Zeta23.MuFields.re_digamma_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T07:11:21.711757+00:00
-- url     : https://prove2.me/submissions/d2b4988f-f166-4475-8b10-c1489e4b2dee

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_GammaFacts_Series
import Theorems.Thm_Zeta23_DigammaSeries_summable_digamma_series
import Theorems.Thm_Zeta23_MuFields_re_digamma_vertical
import Theorems.Thm_Zeta23_MuFields_re_term_eq

-- from Zeta23.GammaFacts.Mu
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/GammaFacts/Mu.lean — the remaining H-Γ fields from the digamma series.  Canonical text: the paper [eq:mufacts]:
"μ is even, smooth, increasing in |τ|, μ ≥ μ(0) > −1, μ(τ) = (1/2π)log(|τ|/2π)
+ O(τ⁻²), μ′(τ) ≪ |τ|⁻¹ (|τ| ≥ 1)" plus the [eq:muints] integrals.
The ψ-toolkit is developed at a parametrized abscissa
a ∈ (0,1) (covers ζ's a = 1/4 and, composed with the recurrence, Theorem E's
a = 1/4 + κ/2).  Foundation: Zeta23.DigammaSeries.
-/

noncomputable section

namespace Zeta23
namespace MuFields

open Complex Filter Topology

variable {a : ℝ}

/-- Points a + it with a ∈ (0,1) avoid the integers. -/
lemma abscissa_mem (ha0 : 0 < a) (ha1 : a < 1) (t : ℝ) :
    ((a : ℂ) + Complex.I * (t : ℂ)) ∈ Complex.integerComplement := by
  rintro ⟨k, hk⟩
  have hre := congrArg Complex.re hk
  simp at hre
  have h0 : (0 : ℤ) < k := by
    have h : (0 : ℝ) < (k : ℝ) := by rw [hre]; exact ha0
    exact_mod_cast h
  have h1 : k < 1 := by
    have h : (k : ℝ) < 1 := by rw [hre]; exact ha1
    exact_mod_cast h
  omega



/-- Summability of the real series. -/
lemma summable_re_terms (ha0 : 0 < a) (ha1 : a < 1) (t : ℝ) :
    Summable (fun n : ℕ =>
      1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t ^ 2)) := by
  have hs := Zeta23.DigammaSeries.summable_digamma_series (abscissa_mem ha0 ha1 t)
  have hmap := hs.map Complex.reCLM Complex.continuous_re
  refine hmap.congr fun n => ?_
  exact re_term_eq t n


/-! ### Monotonicity on the vertical line, and the μ order facts -/






/-! ### The derivative bound μ′ ≪ 1/|τ|  (via the trigamma series) -/




end MuFields
end Zeta23
end
open Zeta23
open MuFields
open Complex Filter Topology
variable {a : ℝ}

theorem solution (ha0 : 0 < a) (ha1 : a < 1) :
    MonotoneOn (fun t : ℝ => (Complex.digamma ((a : ℂ) + Complex.I * t)).re)
      (Set.Ici (0 : ℝ)) := by
  intro t₁ h₁ t₂ h₂ h12
  simp only
  rw [re_digamma_vertical ha0 ha1, re_digamma_vertical ha0 ha1]
  have ht1 : (0 : ℝ) ≤ t₁ := h₁
  have hsq : t₁ ^ 2 ≤ t₂ ^ 2 := by nlinarith
  have hmono1 : a / (a ^ 2 + t₂ ^ 2) ≤ a / (a ^ 2 + t₁ ^ 2) :=
    div_le_div_of_nonneg_left ha0.le (by positivity) (by linarith)
  have hterm : ∀ n : ℕ,
      (1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t₁ ^ 2))
        ≤ 1 / ((n : ℝ) + 1) - ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t₂ ^ 2) := by
    intro n
    have hna : (0 : ℝ) < (n : ℝ) + 1 + a := by positivity
    have h2 : ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t₂ ^ 2)
        ≤ ((n : ℝ) + 1 + a) / (((n : ℝ) + 1 + a) ^ 2 + t₁ ^ 2) :=
      div_le_div_of_nonneg_left hna.le (by positivity) (by linarith)
    linarith
  have hsum := (summable_re_terms ha0 ha1 t₁).tsum_le_tsum hterm
    (summable_re_terms ha0 ha1 t₂)
  linarith
