-- Prove2me | solution 1 for Zeta23.WeilEF.digamma_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T04:19:46.382819+00:00
-- url     : https://prove2.me/submissions/973cfab6-3aee-4f69-9c26-2ce811ea960b

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
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
import Theorems.Thm_Zeta23_DigammaSeries_hasSum_digamma_series

-- from Zeta23.WeilEF.GammaRBracket
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/GammaRBracket.lean — the critical-line Γℝ bracket; proves
`Zeta23.WeilEF.gammaR_bracket`:

  logDeriv Γℝ(1/2+it) + logDeriv Γℝ(1/2−it) = Re ψ(1/4 + it/2) − log π      (t ∈ ℝ),

from Γℝ(s) = π^{−s/2}Γ(s/2) (Mathlib `Complex.Gammaℝ`), logDeriv Γℝ(s) = −(log π)/2 + ψ(s/2)/2
for re s > 0, and the conjugation symmetry ψ(conj z) = conj ψ(z) (from the partial-fraction
series Zeta23.DigammaSeries.hasSum_digamma_series).
-/

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex




end WeilEF
end Zeta23
end
open Zeta23
open Complex

theorem solution {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    Complex.digamma (starRingEnd ℂ z) = starRingEnd ℂ (Complex.digamma z) := by
  have hz' : starRingEnd ℂ z ∈ Complex.integerComplement := by
    rintro ⟨k, hk⟩
    apply hz
    refine ⟨k, ?_⟩
    have := congrArg (starRingEnd ℂ) hk
    simpa using this
  have h1 := Zeta23.DigammaSeries.hasSum_digamma_series hz
  have h2 := Zeta23.DigammaSeries.hasSum_digamma_series hz'
  -- conj of the series for z is the series for conj z
  have h1c : HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) - 1 / (starRingEnd ℂ z + n + 1))
      (starRingEnd ℂ (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z)) := by
    have := (Complex.hasSum_conj' ).mpr h1
    refine this.congr_fun fun n => ?_
    simp only [map_sub, map_div₀, map_one, map_add, map_natCast]
  have huniq := h2.unique h1c
  have e : starRingEnd ℂ (Complex.digamma z + (Real.eulerMascheroniConstant : ℂ) + 1 / z)
      = starRingEnd ℂ (Complex.digamma z) + (Real.eulerMascheroniConstant : ℂ)
        + 1 / starRingEnd ℂ z := by
    simp only [map_add, map_div₀, map_one, Complex.conj_ofReal]
  rw [e] at huniq
  linear_combination huniq
