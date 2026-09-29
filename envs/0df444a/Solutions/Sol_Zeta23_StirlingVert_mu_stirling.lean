-- Prove2me | solution 1 for Zeta23.StirlingVert.mu_stirling
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:12:18.375068+00:00
-- url     : https://prove2.me/submissions/f5cc0fee-91b0-43c7-93da-1f5773bf7b53

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
import Theorems.Thm_Zeta23_StirlingVert_re_digamma_stirlingPrime

-- from Zeta23.GammaFacts.Mu
section
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






/-! ### Monotonicity on the vertical line, and the μ order facts -/


/-- Bridge to Zeta23.mu: μ(τ) in terms of the parametrized line at a = 1/4, t = τ/2. -/
lemma mu_eq (τ : ℝ) :
    Zeta23.mu τ = (1 / (2 * Real.pi))
        * (Complex.digamma ((((1 : ℝ) / 4 : ℝ) : ℂ) + Complex.I * ((τ / 2 : ℝ) : ℂ))).re
      - Real.log Real.pi / (2 * Real.pi) := by
  unfold Zeta23.mu
  congr 3
  push_cast
  ring




/-! ### The derivative bound μ′ ≪ 1/|τ|  (via the trigamma series) -/




end MuFields
end Zeta23
end
end

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

theorem solution : ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ |τ| →
    |Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi))| ≤ C / τ ^ 2 := by
  refine ⟨20 / (2 * Real.pi), fun τ hτ => ?_⟩
  have hπ := Real.pi_pos
  have ht : 1 / 2 ≤ |τ / 2| := by rw [abs_div, abs_two]; linarith
  have h := re_digamma_stirlingPrime (a := 1 / 4) (by norm_num) (by norm_num) ht
  have hτ0 : 0 < |τ| := by linarith
  set D : ℝ := (Complex.digamma ((((1:ℝ) / 4 : ℝ)) + Complex.I * ((τ / 2 : ℝ) : ℂ))).re
    - Real.log |τ / 2| with hD
  have hD5 : |D| ≤ 5 / (τ / 2) ^ 2 := h
  -- μ τ − (1/2π)log(|τ|/2π) = (1/2π) · D
  have hlogs : Real.log (|τ| / (2 * Real.pi)) = Real.log |τ / 2| - Real.log Real.pi := by
    rw [abs_div, abs_two, Real.log_div hτ0.ne' (by positivity), Real.log_div hτ0.ne' two_ne_zero,
      Real.log_mul two_ne_zero hπ.ne']
    ring
  have key : Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (|τ| / (2 * Real.pi))
      = (1 / (2 * Real.pi)) * D := by
    rw [Zeta23.MuFields.mu_eq τ, hlogs, hD]
    ring
  rw [key, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / (2 * Real.pi))]
  calc 1 / (2 * Real.pi) * |D| ≤ 1 / (2 * Real.pi) * (5 / (τ / 2) ^ 2) := by gcongr
    _ = 20 / (2 * Real.pi) / τ ^ 2 := by field_simp; ring
