-- Prove2me | solution 1 for Zeta23.StirlingVert.re_digamma_stirlingPrime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:13:36.54475+00:00
-- url     : https://prove2.me/submissions/02a560a1-1d74-4d87-8db5-da5d31908510

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
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_GammaFacts_Series
import Definitions.Def_Zeta23_GammaFacts_StirlingVert
import Theorems.Thm_Zeta23_StirlingVert_re_digamma_stirling

-- from Zeta23.GammaFacts.StirlingVert
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/GammaFacts/StirlingVert.lean — Stirling for the digamma function on vertical lines.  Target: the H-Γ field `GammaFacts.stirling`
  "μ(τ) = (1/2π) log(|τ|/2π) + O(τ⁻²)  (|τ| ≥ 1)"   [eq:mufacts]
via the COMPLEX asymptotic  ψ(w) = log w − 1/(2w) + O(1/(Im w)²)  for 0 < Re w ≤ 1,
|Im w| ≥ 1, proved from the partial-fraction series (Zeta23.DigammaSeries)
WITHOUT Euler–Maclaurin:  on each unit interval
   1/(x+w) = 1/(m+w) − (x−m)/(m+w)² + (x−m)²/((m+w)²(x+w))        (exact algebra),
so ∫_m^{m+1} dx/(x+w) = 1/(m+w) − 1/(2(m+w)²) + ε_m, |ε_m| ≤ 1/(3|m+w|²|Im w|), while the
left side is log(m+1+w) − log(m+w) (FTC for Complex.log on the slit plane) and telescopes.
-/

noncomputable section

namespace Zeta23
namespace StirlingVert

open Complex Filter Topology MeasureTheory intervalIntegral Set

/-! ### ℂ-specialized interval-integral constant rules (the RCLike-generic Mathlib versions do
not match ℂ's default instance path under `rw`; cf. Zeta23.integral_const_mul_C) -/



/-! ### Elementary bounds for points in the right half-plane -/





/-! ### The antiderivative `F(x) = log(x + w)` on `[0, ∞)` -/



/-! ### The per-interval expansion -/





/-! ### The sequence `z_n := n + 1 + w` -/

section Seq
variable {w : ℂ}












/-! ### Bounds: `Σ_{n<N} 1/‖z_n‖² ≤ 2/|im w|` by a real telescoping -/




/-! ### Summability of the remainders and tsum bounds -/









/-! ### Limits -/



/-! ### The exact identity and the Stirling bound -/





end Seq

/-! ### Real part on vertical lines, and the H-Γ field for μ -/

section RePart




end RePart

end StirlingVert
end Zeta23
end
open Zeta23
open StirlingVert
open Complex Filter Topology MeasureTheory intervalIntegral Set

theorem solution {a : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1) {t : ℝ} (ht : 1 / 2 ≤ |t|) :
    |(Complex.digamma ((a : ℂ) + Complex.I * t)).re - Real.log (abs t)| ≤ 5 / t ^ 2 := by
  have h := re_digamma_stirling ha0 ha1 ht
  have ht0 : 0 < |t| := by linarith
  have ht2 : 0 < t ^ 2 := by rw [← sq_abs]; positivity
  -- ½log(a²+t²) − log|t| = ½ log(1 + a²/t²) ∈ [0, a²/(2t²)]
  have hl : (1 / 2) * Real.log (a ^ 2 + t ^ 2) - Real.log (abs t)
      = (1 / 2) * Real.log (1 + a ^ 2 / t ^ 2) := by
    have htne : t ≠ 0 := fun h0 => by rw [h0] at ht0; simp at ht0
    have : a ^ 2 + t ^ 2 = t ^ 2 * (1 + a ^ 2 / t ^ 2) := by field_simp; ring
    rw [this, Real.log_mul ht2.ne' (by positivity), ← sq_abs, Real.log_pow]
    push_cast; ring
  have hb : |(1 / 2) * Real.log (a ^ 2 + t ^ 2) - Real.log (abs t)| ≤ 1 / t ^ 2 := by
    have hx0 : 0 ≤ a ^ 2 / t ^ 2 := by positivity
    have hlog0 : 0 ≤ Real.log (1 + a ^ 2 / t ^ 2) := Real.log_nonneg (by linarith)
    have hlog := Real.log_le_sub_one_of_pos (by positivity : (0:ℝ) < 1 + a ^ 2 / t ^ 2)
    have ha2 : a ^ 2 / t ^ 2 ≤ 1 / t ^ 2 := by
      apply div_le_div_of_nonneg_right _ ht2.le; nlinarith
    rw [hl, abs_of_nonneg (by positivity)]
    linarith
  calc |(Complex.digamma ((a : ℂ) + Complex.I * t)).re - Real.log (abs t)|
      ≤ |(Complex.digamma ((a : ℂ) + Complex.I * t)).re - (1 / 2) * Real.log (a ^ 2 + t ^ 2)|
        + |(1 / 2) * Real.log (a ^ 2 + t ^ 2) - Real.log (abs t)| := abs_sub_le _ _ _
    _ ≤ 4 / t ^ 2 + 1 / t ^ 2 := add_le_add h hb
    _ = 5 / t ^ 2 := by ring
