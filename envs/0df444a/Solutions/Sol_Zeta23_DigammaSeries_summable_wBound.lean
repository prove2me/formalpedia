-- Prove2me | solution 1 for Zeta23.DigammaSeries.summable_wBound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T08:06:47.319846+00:00
-- url     : https://prove2.me/submissions/54b5febe-bab9-41bd-9731-760e2ae87385

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

-- from Zeta23.GammaFacts.Series
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/GammaFacts/Series.lean — the digamma partial-fraction series.

Target:  digamma z = −γ − 1/z + ∑'_{n≥0} (1/(n+1) − 1/(z+n+1))   for z ∈ ℂ_ℤ,
the Mathlib-missing piece needed for the remaining H-Γ fields
([eq:mufacts]; see Zeta23/GammaFacts.lean).  Route (modelled on Mathlib's
Analysis/SpecialFunctions/Trigonometric/Cotangent.lean, which does the same for
sin → cot):
  1. Weierstrass factors  1 + wTerm n z = (1 + z/(n+1))·e^{−z/(n+1)}, with
     ‖wTerm n z‖ ≤ 3(‖z‖/(n+1))² for n+1 ≥ ‖z‖  (M-test input);
  2. the finite identity  (GammaSeq z N)⁻¹ = z·e^{(H_N − log N)z}·∏_{n<N}(1+wTerm n z);
  3. N → ∞ (GammaSeq_tendsto_Gamma + tendsto_harmonic_sub_log):
       Γ(z)⁻¹ = z·e^{γz}·∏'_n (1 + wTerm n z)            [Weierstrass product]
  4. logDeriv via Complex.logDeriv_tprod_eq_tsum          [digamma series].
This file has steps 1–3; step 4 is `digamma_series` at the bottom.
-/

noncomputable section

namespace Zeta23
namespace DigammaSeries

open Complex Filter Topology








/-! ### The finite identity and the Weierstrass product -/








end DigammaSeries
end Zeta23
end
open Zeta23
open DigammaSeries
open Complex Filter Topology

theorem solution (R : ℝ) : Summable (fun n : ℕ => 3 * (R / ((n : ℝ) + 1)) ^ 2) := by
  have h1 : Summable (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹) := by
    have h2 : Summable (fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹) := by
      have := Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)
      have heq : (fun n : ℕ => ((n : ℝ) ^ (2 : ℝ))⁻¹) = fun n : ℕ => (((n : ℝ)) ^ 2)⁻¹ := by
        funext n
        rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      rwa [heq] at this
    have := (summable_nat_add_iff 1).mpr h2
    simpa [add_comm] using this
  have h3 : (fun n : ℕ => 3 * (R / ((n : ℝ) + 1)) ^ 2)
      = fun n : ℕ => (3 * R ^ 2) * ((((n : ℝ) + 1) ^ 2)⁻¹) := by
    funext n
    rw [div_pow]
    ring
  rw [h3]
  exact h1.mul_left _
