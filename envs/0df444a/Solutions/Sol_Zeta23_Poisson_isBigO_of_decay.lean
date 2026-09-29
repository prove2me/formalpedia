-- Prove2me | solution 1 for Zeta23.Poisson.isBigO_of_decay
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T06:46:24.101554+00:00
-- url     : https://prove2.me/submissions/c663e157-d619-4007-9134-fdbb88394d80

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Poisson
import Definitions.Def_Zeta23_Taper_Basic

-- from Zeta23.Poisson
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
[lem:poisson] "Poisson summation for the Gabor system", the paper §2.2:

  "For all τ, τ' ∈ ℝ,
     K_∞(τ,τ') := Σ_{k∈ℤ} φ̂(τ−τ_k) φ̂(τ'−τ_k) = L·Φ(τ−τ'),   in particular   Σ_{k∈ℤ} φ̂(τ−τ_k)² = aL²."

Here τ_k := T + k h, h := 2π/L [eq:fk], Φ := (φ²)^ [eq:PhigA], a := L⁻¹∫φ² [eq:abdef], and
φ̂(s) = ∫ φ(u) e^{isu} du is the paper's Fourier convention (`Zeta23.paperFT`).  Only the
real-argument identity is proved (that is all [prop:block](ii) uses; the complex continuation
mentioned in [rem:pairblock] is not used by the proof).

Proof route (the paper's, rearranged so that Fourier inversion is not needed): with
  G(ξ) := L · ∫ φ(u) φ(Lξ−u) e^{i(τu + τ'(Lξ−u) − TLξ)} du      (= L e^{−iTLξ}(φ_τ ∗ φ_{τ'})(Lξ)),
G is continuous with support in [−1,1] and G(k) = 0 for k ∈ ℤ∖{0} (because φ(u) = 0 for
|u| ≥ L/2), G(0) = L ∫ φ(u)φ(−u)e^{i(τ−τ')u} du = L Φ(τ−τ') (φ even), and a Fubini computation
gives 𝓕G(w) = φ̂(τ−τ_w) φ̂(τ'−τ_w) for Mathlib's 𝓕 and every real w (τ_w := T + w·2π/L).
Mathlib's Poisson summation `Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable`
(Σ_k G(k) = Σ_n 𝓕G(n)) then gives the claim; summability of n ↦ φ̂(τ−τ_n)φ̂(τ'−τ_n) comes from
the decay |φ̂(r)| ≪ (1+r²)⁻¹, i.e. [eq:hfbound]/[eq:psidef].
-/

open Complex MeasureTheory Real Set Filter Topology Asymptotics
open scoped FourierTransform

namespace Zeta23

namespace Poisson

/-! #### A decay-to-`IsBigO` lemma -/


/-! #### The auxiliary function `G` -/

variable (φ : ℝ → ℝ) (L T τ τ' : ℝ)



variable {φ L T τ τ'}










/-! #### The abstract identity -/


end Poisson

namespace Taper

variable {ϱ : ℝ → ℝ} {L w : ℝ}




end Taper

namespace Params

variable {P : Params} {T : ℝ}


variable (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
include hP hwL




end Params

end Zeta23
open Complex MeasureTheory Real Set Filter Topology Asymptotics
open scoped FourierTransform
open Zeta23
open Poisson

theorem solution {g : ℝ → ℂ} {c h C : ℝ} (hh : h ≠ 0)
    (hg : ∀ w, ‖g w‖ * (1 + (c - w * h) ^ 2) ≤ C) :
    g =O[cocompact ℝ] fun w : ℝ => |w| ^ (-2 : ℝ) := by
  have hC : 0 ≤ C := le_trans (by positivity) (hg 0)
  refine IsBigO.of_bound (4 * C / h ^ 2) ?_
  have hev : ∀ᶠ w : ℝ in cocompact ℝ, max 1 (2 * |c| / |h|) ≤ ‖w‖ :=
    tendsto_norm_cocompact_atTop.eventually (eventually_ge_atTop _)
  filter_upwards [hev] with w hw
  rw [Real.norm_eq_abs] at hw
  have hw1 : 1 ≤ |w| := le_trans (le_max_left _ _) hw
  have hw2 : 2 * |c| / |h| ≤ |w| := le_trans (le_max_right _ _) hw
  have hhpos : 0 < |h| := abs_pos.mpr hh
  have h1 : |w| * |h| / 2 ≤ |c - w * h| := by
    have h3 : |w * h| - |c| ≤ |c - w * h| := by
      have := abs_sub_abs_le_abs_sub (w * h) c
      rw [abs_sub_comm] at this
      exact this
    rw [abs_mul] at h3
    rw [div_le_iff₀ hhpos] at hw2
    linarith
  have h2 : (|w| * |h| / 2) ^ 2 ≤ 1 + (c - w * h) ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) h1 2
    rw [sq_abs] at this
    linarith
  have hnorm : ‖(|w| ^ (-2 : ℝ) : ℝ)‖ = (w ^ 2)⁻¹ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.rpow_neg (abs_nonneg _),
      Real.rpow_two, sq_abs]
  rw [hnorm]
  have hden : 0 < 1 + (c - w * h) ^ 2 := by positivity
  have hq : 0 < (|w| * |h| / 2) ^ 2 := by positivity
  have hw0 : w ≠ 0 := by intro h0; rw [h0, abs_zero] at hw1; linarith
  calc ‖g w‖ ≤ C / (1 + (c - w * h) ^ 2) := by rw [le_div_iff₀ hden]; exact hg w
    _ ≤ C / ((|w| * |h| / 2) ^ 2) := by gcongr
    _ = 4 * C / h ^ 2 * (w ^ 2)⁻¹ := by
      rw [div_pow, mul_pow, sq_abs, sq_abs]
      field_simp
      ring
