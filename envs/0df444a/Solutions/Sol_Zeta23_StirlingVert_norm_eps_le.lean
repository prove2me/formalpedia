-- Prove2me | solution 1 for Zeta23.StirlingVert.norm_eps_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:20:54.460434+00:00
-- url     : https://prove2.me/submissions/43a60f86-918c-450e-8c6f-198ececaf10b

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

/-- for `x ≥ 0` real and `0 < re w`: `‖x + w‖ ≥ |im w|`. -/
theorem abs_im_le_norm_add {w : ℂ} (x : ℝ) : |w.im| ≤ ‖(x : ℂ) + w‖ := by
  have := Complex.abs_im_le_norm ((x : ℂ) + w)
  simpa using this

theorem re_add_pos {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) : 0 < ((x : ℂ) + w).re := by
  simp; linarith


theorem add_ne_zero {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) : (x : ℂ) + w ≠ 0 :=
  fun h => by have := re_add_pos hw hx; rw [h] at this; simp at this

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

theorem solution {w : ℂ} (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) {m : ℝ} (hm : 0 ≤ m) :
    ‖eps w m‖ ≤ 1 / (3 * ‖(m : ℂ) + w‖ ^ 2 * |w.im|) := by
  have hmw := add_ne_zero hw hm
  have hM : 0 < ‖(m : ℂ) + w‖ := norm_pos_iff.mpr hmw
  have ht0 : 0 < |w.im| := by linarith
  unfold eps
  calc ‖∫ x in m..(m + 1), ((x - m : ℝ) : ℂ) ^ 2 / (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w))‖
      ≤ ∫ x in m..(m + 1), ‖((x - m : ℝ) : ℂ) ^ 2 / (((m : ℂ) + w) ^ 2 * ((x : ℂ) + w))‖ :=
        intervalIntegral.norm_integral_le_integral_norm (by linarith)
    _ ≤ ∫ x in m..(m + 1), (x - m) ^ 2 / (‖(m : ℂ) + w‖ ^ 2 * |w.im|) := by
        apply intervalIntegral.integral_mono_on (by linarith)
        · refine (ContinuousOn.intervalIntegrable ?_).norm
          apply ContinuousOn.div (by fun_prop) (by fun_prop)
          intro x hx
          rw [uIcc_of_le (by linarith)] at hx
          exact mul_ne_zero (pow_ne_zero _ hmw) (add_ne_zero hw (by linarith [hx.1]))
        · exact (by fun_prop : Continuous fun x : ℝ => (x - m) ^ 2 / (‖(m : ℂ) + w‖ ^ 2 * |w.im|))
            |>.intervalIntegrable _ _
        · intro x hx
          have hx0 : 0 ≤ x := by linarith [hx.1]
          have hxw : |w.im| ≤ ‖(x : ℂ) + w‖ := abs_im_le_norm_add x
          rw [norm_div, norm_mul, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
            sq_abs]
          apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
          exact mul_le_mul_of_nonneg_left hxw (by positivity)
    _ = 1 / (3 * ‖(m : ℂ) + w‖ ^ 2 * |w.im|) := by
        rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_right (fun u : ℝ => u ^ 2) m]
        simp only [sub_self, add_sub_cancel_left, integral_pow]
        norm_num
        field_simp
