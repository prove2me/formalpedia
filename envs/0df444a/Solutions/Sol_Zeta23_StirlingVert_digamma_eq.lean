-- Prove2me | solution 1 for Zeta23.StirlingVert.digamma_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:16:52.90946+00:00
-- url     : https://prove2.me/submissions/4af605bc-c33d-45b4-b8fd-6321916b5279

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
import Theorems.Thm_Zeta23_DigammaSeries_hasSum_digamma_series
import Theorems.Thm_Zeta23_StirlingVert_norm_eps_le
import Theorems.Thm_Zeta23_StirlingVert_partial_sum_eq
import Theorems.Thm_Zeta23_StirlingVert_tendsto_harmonic_sub_clog

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

theorem natp1_re_pos (hw : 0 < w.re) (n : ℕ) : 0 < ((n : ℂ) + 1 + w).re := by
  simp; positivity

theorem natp1_ne_zero (hw : 0 < w.re) (n : ℕ) : (n : ℂ) + 1 + w ≠ 0 := fun h => by
  have := natp1_re_pos hw n; rw [h] at this; simp at this


theorem natp1_le_norm (hw : 0 < w.re) (n : ℕ) : (n : ℝ) + 1 ≤ ‖(n : ℂ) + 1 + w‖ := by
  have h := Complex.re_le_norm ((n : ℂ) + 1 + w)
  simp at h; linarith





theorem norm_rho_le (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) (n : ℕ) :
    ‖rho w n‖ ≤ 1 / (‖(n : ℂ) + 1 + w‖ ^ 2 * |w.im|) := by
  have h1 := natp1_ne_zero hw n
  have hn2 : |w.im| ≤ ‖(n : ℂ) + 2 + w‖ := by
    have := Complex.abs_im_le_norm ((n : ℂ) + 2 + w); simpa using this
  have ht0 : 0 < |w.im| := by linarith
  unfold rho
  rw [norm_div, norm_one, norm_mul, norm_pow]
  apply div_le_div_of_nonneg_left zero_le_one (by positivity)
  exact mul_le_mul_of_nonneg_left hn2 (by positivity)

theorem norm_eps_natp1_le (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) (n : ℕ) :
    ‖eps w ((n : ℝ) + 1)‖ ≤ 1 / (3 * ‖(n : ℂ) + 1 + w‖ ^ 2 * |w.im|) := by
  have := norm_eps_le hw ht (m := (n : ℝ) + 1) (by positivity)
  rw [show ((((n : ℝ) + 1 : ℝ)) : ℂ) + w = (n : ℂ) + 1 + w by push_cast; ring] at this
  exact this


/-! ### Bounds: `Σ_{n<N} 1/‖z_n‖² ≤ 2/|im w|` by a real telescoping -/




/-! ### Summability of the remainders and tsum bounds -/

theorem summable_inv_norm_sq (hw : 0 < w.re) :
    Summable (fun n : ℕ => 1 / ‖(n : ℂ) + 1 + w‖ ^ 2) := by
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have := (Real.summable_one_div_nat_pow.mpr one_lt_two)
    exact_mod_cast (summable_nat_add_iff 1).mpr this
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  exact div_le_div_of_nonneg_left zero_le_one (by positivity)
    (pow_le_pow_left₀ (by positivity) (natp1_le_norm hw n) 2)

theorem summable_rho (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) : Summable (rho w) := by
  refine Summable.of_norm_bounded ((summable_inv_norm_sq hw).mul_left (1 / |w.im|)) fun n => ?_
  refine le_trans (norm_rho_le hw ht n) (le_of_eq ?_)
  field_simp

theorem summable_eps (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    Summable (fun n : ℕ => eps w ((n : ℝ) + 1)) := by
  refine Summable.of_norm_bounded ((summable_inv_norm_sq hw).mul_left (1 / (3 * |w.im|)))
    fun n => ?_
  refine le_trans (norm_eps_natp1_le hw ht n) (le_of_eq ?_)
  field_simp






/-! ### Limits -/


theorem tendsto_inv_natp1 (hw : 0 < w.re) :
    Tendsto (fun N : ℕ => ((N : ℂ) + 1 + w)⁻¹) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    tendsto_one_div_add_atTop_nhds_zero_nat (fun N => norm_nonneg _) (fun N => ?_)
  rw [norm_inv]
  have h := natp1_le_norm hw N
  have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  rw [inv_eq_one_div]
  exact one_div_le_one_div_of_le hpos h

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
variable {w : ℂ}

theorem solution (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    Complex.digamma w = Complex.log (1 + w) - 1 / w - (1 / 2 : ℂ) * (1 + w)⁻¹
      - (1 / 2 : ℂ) * (∑' n, rho w n) + ∑' n : ℕ, eps w ((n : ℝ) + 1) := by
  have hmem : w ∈ Complex.integerComplement := by
    rintro ⟨k, hk⟩
    have := congrArg Complex.im hk
    simp at this
    rw [← this] at ht; simp at ht; linarith
  have hL := (Zeta23.DigammaSeries.hasSum_digamma_series hmem).tendsto_sum_nat
  -- the same partial sums, rearranged
  have hR : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, (1 / ((n : ℂ) + 1) - 1 / (w + n + 1)))
      atTop (𝓝 ((Real.eulerMascheroniConstant : ℂ) + Complex.log (1 + w)
        - (1 / 2 : ℂ) * ((1 + w)⁻¹ - 0 + ∑' n, rho w n) + ∑' n : ℕ, eps w ((n : ℝ) + 1))) := by
    have e : ∀ N : ℕ, ∑ n ∈ Finset.range N, (1 / ((n : ℂ) + 1) - 1 / (w + n + 1))
        = ((∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1)) - Complex.log ((N : ℂ) + 1 + w))
          + Complex.log (1 + w)
          - (1 / 2 : ℂ) * ((1 + w)⁻¹ - ((N : ℂ) + 1 + w)⁻¹ + ∑ n ∈ Finset.range N, rho w n)
          + ∑ n ∈ Finset.range N, eps w ((n : ℝ) + 1) := by
      intro N
      rw [partial_sum_eq hw N]
      push_cast
      ring
    simp_rw [e]
    refine (((tendsto_harmonic_sub_clog hw).add tendsto_const_nhds).sub
      (((tendsto_const_nhds.sub (tendsto_inv_natp1 hw)).add
        (summable_rho hw ht).hasSum.tendsto_sum_nat).const_mul _)).add
      (summable_eps hw ht).hasSum.tendsto_sum_nat
  have := tendsto_nhds_unique hL hR
  rw [sub_zero] at this
  linear_combination this
