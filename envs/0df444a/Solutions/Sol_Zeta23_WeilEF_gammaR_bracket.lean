-- Prove2me | solution 1 for Zeta23.WeilEF.gammaR_bracket
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T04:19:02.832793+00:00
-- url     : https://prove2.me/submissions/aeadfdd7-b162-4202-a455-b4f2b4a7ecbe

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
import Theorems.Thm_Zeta23_WeilEF_digamma_conj
import Theorems.Thm_Zeta23_WeilEF_logDeriv_GammaR

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
open WeilEF
open Complex

theorem solution (t : ℝ) :
    logDeriv Complex.Gammaℝ (1/2 + t * I) + logDeriv Complex.Gammaℝ (1/2 - t * I)
      = (((Complex.digamma (1/4 + t/2 * I)).re - Real.log Real.pi : ℝ) : ℂ) := by
  have hp : 0 < ((1:ℂ)/2 + t * I).re := by simp
  have hm : 0 < ((1:ℂ)/2 - t * I).re := by simp
  rw [logDeriv_GammaR hp, logDeriv_GammaR hm]
  set w : ℂ := 1/4 + t/2 * I with hw
  have e1 : ((1:ℂ)/2 + t * I) / 2 = w := by rw [hw]; ring
  have e2 : ((1:ℂ)/2 - t * I) / 2 = starRingEnd ℂ w := by
    have : starRingEnd ℂ w = 1/4 - t/2 * I := by
      rw [hw, show (1:ℂ)/4 + (t:ℂ)/2 * I = ((1/4:ℝ):ℂ) + ((t/2:ℝ):ℂ) * I by push_cast; ring]
      simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
      push_cast; ring
    rw [this]; ring
  have hwZ : w ∈ Complex.integerComplement := by
    rintro ⟨k, hk⟩
    have := congrArg Complex.re hk
    rw [hw] at this
    simp at this
    -- (k : ℝ) = 1/4 is impossible
    have h4 : (4 * k : ℤ) = (1 : ℤ) := by
      have : (4 : ℝ) * k = 1 := by rw [this]; norm_num
      exact_mod_cast this
    omega
  rw [e1, e2, digamma_conj hwZ]
  -- ψ(w)/2 + conj ψ(w)/2 = Re ψ(w)
  have hre : (1/2 : ℂ) * Complex.digamma w + (1/2 : ℂ) * starRingEnd ℂ (Complex.digamma w)
      = ((Complex.digamma w).re : ℂ) := by
    rw [← mul_add, Complex.add_conj]; push_cast; ring
  push_cast
  linear_combination hre
