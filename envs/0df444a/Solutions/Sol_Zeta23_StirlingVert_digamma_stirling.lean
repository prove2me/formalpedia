-- Prove2me | solution 1 for Zeta23.StirlingVert.digamma_stirling
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:15:26.446004+00:00
-- url     : https://prove2.me/submissions/9827dfcf-2988-442e-b5f3-b4c0e6850bf9

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
import Theorems.Thm_Zeta23_StirlingVert_digamma_eq
import Theorems.Thm_Zeta23_StirlingVert_integral_inv_add_eq
import Theorems.Thm_Zeta23_StirlingVert_norm_eps_le

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


theorem re_add_pos {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) : 0 < ((x : ℂ) + w).re := by
  simp; linarith

theorem add_mem_slitPlane {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) :
    (x : ℂ) + w ∈ Complex.slitPlane :=
  Complex.mem_slitPlane_iff.mpr (Or.inl (re_add_pos hw hx))

theorem add_ne_zero {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) : (x : ℂ) + w ≠ 0 :=
  fun h => by have := re_add_pos hw hx; rw [h] at this; simp at this

/-! ### The antiderivative `F(x) = log(x + w)` on `[0, ∞)` -/

theorem hasDerivAt_log_add {w : ℂ} (hw : 0 < w.re) {x : ℝ} (hx : 0 ≤ x) :
    HasDerivAt (fun y : ℝ => Complex.log ((y : ℂ) + w)) (((x : ℂ) + w)⁻¹) x := by
  have h1 : HasDerivAt (fun z : ℂ => Complex.log (z + w)) (((x : ℂ) + w)⁻¹) (x : ℂ) := by
    have := (Complex.hasDerivAt_log (add_mem_slitPlane hw hx)).comp (x : ℂ)
      ((hasDerivAt_id (x : ℂ)).add_const w)
    simpa [Function.comp_def] using this
  exact h1.comp_ofReal

/-- FTC: `∫_m^{m+1} dx/(x+w) = log(m+1+w) − log(m+w)` for `m ≥ 0`. -/
theorem integral_inv_add_eq_log_sub {w : ℂ} (hw : 0 < w.re) {m : ℝ} (hm : 0 ≤ m) :
    ∫ x in m..(m + 1), ((x : ℂ) + w)⁻¹
      = Complex.log (((m + 1 : ℝ) : ℂ) + w) - Complex.log ((m : ℂ) + w) := by
  have hcont : ContinuousOn (fun x : ℝ => ((x : ℂ) + w)⁻¹) (uIcc m (m + 1)) := by
    apply ContinuousOn.inv₀ (by fun_prop)
    intro x hx
    rw [uIcc_of_le (by linarith)] at hx
    exact add_ne_zero hw (by linarith [hx.1])
  rw [integral_eq_sub_of_hasDerivAt (f := fun y : ℝ => Complex.log ((y : ℂ) + w))
    (fun x hx => by
      rw [uIcc_of_le (by linarith)] at hx
      exact hasDerivAt_log_add hw (by linarith [hx.1]))
    (hcont.intervalIntegrable)]

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

theorem norm_sq_natp1_ge (hw : 0 < w.re) (n : ℕ) :
    ((n : ℝ) + 1) ^ 2 + w.im ^ 2 ≤ ‖(n : ℂ) + 1 + w‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hre : ((n : ℂ) + 1 + w).re = (n : ℝ) + 1 + w.re := by simp
  have him : ((n : ℂ) + 1 + w).im = w.im := by simp
  rw [hre, him]
  nlinarith

theorem inv_norm_sq_le_telescope (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) (n : ℕ) :
    1 / ‖(n : ℂ) + 1 + w‖ ^ 2 ≤ 2 * (1 / ((n : ℝ) + |w.im|) - 1 / ((n : ℝ) + 1 + |w.im|)) := by
  have h1 := norm_sq_natp1_ge hw n
  have ht0 : 0 < |w.im| := by linarith
  have hpos : 0 < ((n : ℝ) + 1) ^ 2 + w.im ^ 2 := by positivity
  have htele : 1 / ((n : ℝ) + |w.im|) - 1 / ((n : ℝ) + 1 + |w.im|)
      = 1 / (((n : ℝ) + |w.im|) * ((n : ℝ) + 1 + |w.im|)) := by
    field_simp; ring
  rw [htele]
  have hsq : w.im ^ 2 = |w.im| ^ 2 := (sq_abs _).symm
  calc 1 / ‖(n : ℂ) + 1 + w‖ ^ 2 ≤ 1 / (((n : ℝ) + 1) ^ 2 + w.im ^ 2) :=
        div_le_div_of_nonneg_left zero_le_one hpos h1
    _ ≤ 2 * (1 / (((n : ℝ) + |w.im|) * ((n : ℝ) + 1 + |w.im|))) := by
        rw [hsq, ← div_eq_mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [sq_nonneg ((n : ℝ) + 1 - |w.im|)]

theorem sum_inv_norm_sq_le (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) (N : ℕ) :
    ∑ n ∈ Finset.range N, 1 / ‖(n : ℂ) + 1 + w‖ ^ 2 ≤ 2 / |w.im| := by
  have ht0 : 0 < |w.im| := by linarith
  calc ∑ n ∈ Finset.range N, 1 / ‖(n : ℂ) + 1 + w‖ ^ 2
      ≤ ∑ n ∈ Finset.range N, 2 * (1 / ((n : ℝ) + |w.im|) - 1 / ((n : ℝ) + 1 + |w.im|)) :=
        Finset.sum_le_sum fun n _ => inv_norm_sq_le_telescope hw ht n
    _ = 2 * (1 / |w.im| - 1 / ((N : ℝ) + |w.im|)) := by
        rw [← Finset.mul_sum, Finset.sum_congr rfl (fun (i : ℕ) _ => by
          rw [show ((i : ℝ) + 1 + |w.im|) = (((i + 1 : ℕ) : ℝ) + |w.im|) by push_cast; ring]),
          Finset.sum_range_sub' (fun n : ℕ => 1 / ((n : ℝ) + |w.im|)) N]
        push_cast
        ring
    _ ≤ 2 / |w.im| := by
        have : 0 ≤ 1 / ((N : ℝ) + |w.im|) := by positivity
        rw [div_eq_mul_one_div 2]
        linarith

/-! ### Summability of the remainders and tsum bounds -/

theorem summable_inv_norm_sq (hw : 0 < w.re) :
    Summable (fun n : ℕ => 1 / ‖(n : ℂ) + 1 + w‖ ^ 2) := by
  have hs : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) := by
    have := (Real.summable_one_div_nat_pow.mpr one_lt_two)
    exact_mod_cast (summable_nat_add_iff 1).mpr this
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
  exact div_le_div_of_nonneg_left zero_le_one (by positivity)
    (pow_le_pow_left₀ (by positivity) (natp1_le_norm hw n) 2)



theorem summable_norm_rho (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) : Summable (fun n => ‖rho w n‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_inv_norm_sq hw).mul_left (1 / |w.im|))
  refine le_trans (norm_rho_le hw ht n) (le_of_eq ?_)
  field_simp

theorem summable_norm_eps (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    Summable (fun n : ℕ => ‖eps w ((n : ℝ) + 1)‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_inv_norm_sq hw).mul_left (1 / (3 * |w.im|)))
  refine le_trans (norm_eps_natp1_le hw ht n) (le_of_eq ?_)
  field_simp

theorem tsum_inv_norm_sq_le (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    ∑' n : ℕ, 1 / ‖(n : ℂ) + 1 + w‖ ^ 2 ≤ 2 / |w.im| :=
  Real.tsum_le_of_sum_range_le (fun n => by positivity) (sum_inv_norm_sq_le hw ht)

theorem norm_tsum_rho_le (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    ‖∑' n, rho w n‖ ≤ 2 / w.im ^ 2 := by
  have ht0 : 0 < |w.im| := by linarith
  have hS := tsum_inv_norm_sq_le hw ht
  calc ‖∑' n, rho w n‖ ≤ ∑' n, ‖rho w n‖ := norm_tsum_le_tsum_norm (summable_norm_rho hw ht)
    _ ≤ ∑' n : ℕ, (1 / |w.im|) * (1 / ‖(n : ℂ) + 1 + w‖ ^ 2) := by
        refine Summable.tsum_le_tsum (fun n => ?_) (summable_norm_rho hw ht)
          ((summable_inv_norm_sq hw).mul_left _)
        refine le_trans (norm_rho_le hw ht n) (le_of_eq ?_)
        field_simp
    _ = (1 / |w.im|) * ∑' n : ℕ, 1 / ‖(n : ℂ) + 1 + w‖ ^ 2 := tsum_mul_left
    _ ≤ (1 / |w.im|) * (2 / |w.im|) := by gcongr
    _ = 2 / w.im ^ 2 := by rw [← sq_abs]; field_simp

theorem norm_tsum_eps_le (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) :
    ‖∑' n : ℕ, eps w ((n : ℝ) + 1)‖ ≤ (2 / 3) / w.im ^ 2 := by
  have ht0 : 0 < |w.im| := by linarith
  have hS := tsum_inv_norm_sq_le hw ht
  calc ‖∑' n : ℕ, eps w ((n : ℝ) + 1)‖ ≤ ∑' n : ℕ, ‖eps w ((n : ℝ) + 1)‖ :=
        norm_tsum_le_tsum_norm (summable_norm_eps hw ht)
    _ ≤ ∑' n : ℕ, (1 / (3 * |w.im|)) * (1 / ‖(n : ℂ) + 1 + w‖ ^ 2) := by
        refine Summable.tsum_le_tsum (fun n => ?_) (summable_norm_eps hw ht)
          ((summable_inv_norm_sq hw).mul_left _)
        refine le_trans (norm_eps_natp1_le hw ht n) (le_of_eq ?_)
        field_simp
    _ = (1 / (3 * |w.im|)) * ∑' n : ℕ, 1 / ‖(n : ℂ) + 1 + w‖ ^ 2 := tsum_mul_left
    _ ≤ (1 / (3 * |w.im|)) * (2 / |w.im|) := by gcongr
    _ = (2 / 3) / w.im ^ 2 := by rw [← sq_abs]; field_simp

/-! ### Limits -/



/-! ### The exact identity and the Stirling bound -/


/-- `log(1+w) − log w = 1/w − 1/(2w²) + ε_0`. -/
theorem log_one_add_sub_log (hw : 0 < w.re) :
    Complex.log (1 + w) - Complex.log w = w⁻¹ - (1 / 2 : ℂ) / w ^ 2 + eps w 0 := by
  have h1 := integral_inv_add_eq hw (m := 0) le_rfl
  have h2 := integral_inv_add_eq_log_sub hw (m := 0) le_rfl
  rw [h2] at h1
  simpa [add_comm] using h1

theorem norm_eps_zero_le (hw : 0 < w.re) (ht : 1 / 2 ≤ |w.im|) : ‖eps w 0‖ ≤ (1 / 3) / |w.im| ^ 3 := by
  have h := norm_eps_le hw ht (m := 0) le_rfl
  have ht0 : 0 < |w.im| := by linarith
  have hw' : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
  simp only [Complex.ofReal_zero, zero_add] at h
  calc ‖eps w 0‖ ≤ 1 / (3 * ‖w‖ ^ 2 * |w.im|) := h
    _ ≤ 1 / (3 * |w.im| ^ 2 * |w.im|) := by
        apply div_le_div_of_nonneg_left zero_le_one (by positivity)
        gcongr
    _ = (1 / 3) / |w.im| ^ 3 := by field_simp


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
    ‖Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w‖ ≤ 3 / w.im ^ 2 := by
  have hw0 : w ≠ 0 := fun h => by rw [h] at hw; simp at hw
  have h1w : 1 + w ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have ht0 : 0 < |w.im| := by linarith
  have hwn : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
  have h1wn : |w.im| ≤ ‖1 + w‖ := by have := Complex.abs_im_le_norm (1 + w); simpa using this
  have hid := digamma_eq hw ht
  have hlog := log_one_add_sub_log hw
  -- algebra: ψ − log w + 1/(2w) = −1/(2w²(1+w)) + ε₀ − ½Σρ + Σε
  have key : Complex.digamma w - Complex.log w + (1 / 2 : ℂ) / w
      = -(1 / 2 : ℂ) / (w ^ 2 * (1 + w)) + eps w 0
        - (1 / 2 : ℂ) * (∑' n, rho w n) + ∑' n : ℕ, eps w ((n : ℝ) + 1) := by
    rw [hid, show Complex.log (1 + w) = Complex.log w + (w⁻¹ - (1 / 2 : ℂ) / w ^ 2 + eps w 0) by
      rw [← hlog]; ring]
    field_simp
    ring
  rw [key]
  have hsq : |w.im| ^ 2 = w.im ^ 2 := sq_abs _
  have b1 : ‖-(1 / 2 : ℂ) / (w ^ 2 * (1 + w))‖ ≤ (1 / 2) / w.im ^ 2 := by
    rw [norm_div, norm_neg, norm_mul, norm_pow]
    have : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    rw [this, ← hsq]
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have h1 : 1 ≤ ‖1 + w‖ := le_trans (by simp; linarith) (Complex.re_le_norm (1 + w))
    calc |w.im| ^ 2 = |w.im| ^ 2 * 1 := (mul_one _).symm
      _ ≤ ‖w‖ ^ 2 * ‖1 + w‖ := by gcongr
  have b2 : ‖eps w 0‖ ≤ (2 / 3) / w.im ^ 2 := by
    refine le_trans (norm_eps_zero_le hw ht) ?_
    rw [← hsq, div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : |w.im| ^ 3 = |w.im| ^ 2 * |w.im| := by ring
    rw [h3]
    have : 0 < |w.im| ^ 2 := by positivity
    nlinarith
  have b3 : ‖(1 / 2 : ℂ) * ∑' n, rho w n‖ ≤ 1 / w.im ^ 2 := by
    rw [norm_mul, show ‖(1 / 2 : ℂ)‖ = 1 / 2 by norm_num]
    have h := mul_le_mul_of_nonneg_left (norm_tsum_rho_le hw ht) (by norm_num : (0:ℝ) ≤ 1 / 2)
    calc 1 / 2 * ‖∑' n, rho w n‖ ≤ 1 / 2 * (2 / w.im ^ 2) := h
      _ = 1 / w.im ^ 2 := by ring
  have b4 := norm_tsum_eps_le hw ht
  calc ‖-(1 / 2 : ℂ) / (w ^ 2 * (1 + w)) + eps w 0 - (1 / 2 : ℂ) * ∑' n, rho w n
        + ∑' n : ℕ, eps w ((n : ℝ) + 1)‖
      ≤ ‖-(1 / 2 : ℂ) / (w ^ 2 * (1 + w))‖ + ‖eps w 0‖ + ‖(1 / 2 : ℂ) * ∑' n, rho w n‖
        + ‖∑' n : ℕ, eps w ((n : ℝ) + 1)‖ := by
        have s1 := norm_add_le (-(1 / 2 : ℂ) / (w ^ 2 * (1 + w)) + eps w 0 - (1 / 2 : ℂ) * ∑' n, rho w n)
          (∑' n : ℕ, eps w ((n : ℝ) + 1))
        have s2 := norm_sub_le (-(1 / 2 : ℂ) / (w ^ 2 * (1 + w)) + eps w 0) ((1 / 2 : ℂ) * ∑' n, rho w n)
        have s3 := norm_add_le (-(1 / 2 : ℂ) / (w ^ 2 * (1 + w))) (eps w 0)
        linarith
    _ ≤ (1 / 2) / w.im ^ 2 + (2 / 3) / w.im ^ 2 + 1 / w.im ^ 2 + (2 / 3) / w.im ^ 2 := by
        gcongr
    _ ≤ 3 / w.im ^ 2 := by
        have hpos : 0 < w.im ^ 2 := by rw [← hsq]; positivity
        rw [show (1 / 2) / w.im ^ 2 + (2 / 3) / w.im ^ 2 + 1 / w.im ^ 2 + (2 / 3) / w.im ^ 2
          = (17 / 6) / w.im ^ 2 by ring]
        apply div_le_div_of_nonneg_right _ hpos.le
        norm_num
