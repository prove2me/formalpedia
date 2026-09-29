-- Prove2me | solution 1 for Zeta23.Stirling.differentiableAt_digamma
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T07:15:43.69191+00:00
-- url     : https://prove2.me/submissions/9dbb806b-7cd0-466a-9745-91cdb114061f

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

-- from Zeta23.Analytic.Stirling
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Analytic/Stirling.lean — shared Stirling/digamma asymptotics.

This is the shared home for complex Stirling-type asymptotics of Γ, log Γ and ψ = Γ'/Γ.
Consumers:
  • Zeta23/GammaFacts/Mu.lean: ψ on the vertical line Re = 1/4, error O(1/τ²);
    the trigamma series for the μ′ bound;
  • the Riemann–von Mangoldt argument: Im log Γ(1/4 + iT/2) main term; |Γ| growth
    in strips;
  • the explicit-formula argument: digamma growth on vertical strips.
Builds on Zeta23.GammaFacts.Series: digamma_series, hasSum_digamma_series,
summable_digamma_series, inv_gamma_eq_prod (Weierstrass product for 1/Γ).
-/

noncomputable section

namespace Zeta23
namespace Stirling

open Complex Filter Topology



/- `digamma_growth_strip` (coarse digamma growth on the EF strip) is proved as
   Zeta23.WeilEF.digamma_growth_strip in Zeta23/WeilEF/VerticalLine.lean, which is what
   the consumers (Horizontal.lean, FullLine.lean) use. -/

end Stirling
end Zeta23
end
open Zeta23
open Complex Filter Topology

theorem solution {z : ℂ} (hz : z ∈ Complex.integerComplement) :
    DifferentiableAt ℂ Complex.digamma z := by
  have hopenZ : IsOpen Complex.integerComplement := isOpen_compl_range_intCast
  have hΓan : AnalyticAt ℂ Complex.Gamma z := by
    rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [hopenZ.mem_nhds hz] with w hw
    refine Complex.differentiableAt_Gamma w fun m => ?_
    intro h
    exact hw ⟨-(m : ℤ), by push_cast; rw [h]⟩
  have hzero : ∀ m : ℕ, z ≠ -(m : ℂ) := by
    intro m h
    exact hz ⟨-(m : ℤ), by push_cast; rw [h]⟩
  have hΓne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero hzero
  have hψan : AnalyticAt ℂ Complex.digamma z := by
    have h1 : AnalyticAt ℂ (deriv Complex.Gamma) z := hΓan.deriv
    have h2 := h1.div hΓan hΓne
    exact h2.congr (by
      filter_upwards with w
      rw [Complex.digamma_def, logDeriv_apply]
      rfl)
  exact hψan.differentiableAt
