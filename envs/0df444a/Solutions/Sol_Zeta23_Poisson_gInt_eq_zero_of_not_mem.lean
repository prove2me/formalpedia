-- Prove2me | solution 1 for Zeta23.Poisson.gInt_eq_zero_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T06:50:45.952768+00:00
-- url     : https://prove2.me/submissions/f660fe7f-ae10-4de6-a440-a88189d8fbc3

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
variable (φ : ℝ → ℝ) (L T τ τ' : ℝ)
variable {φ L T τ τ'}

theorem solution (hL : 0 < L) (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0)
    {ξ u : ℝ} (h : ¬ (|ξ| < 1 ∧ |u| < L / 2)) : gInt φ L T τ τ' ξ u = 0 := by
  unfold gInt
  by_cases hu : |u| < L / 2
  · have hξ : 1 ≤ |ξ| := by
      by_contra h'
      exact h ⟨not_le.mp h', hu⟩
    have : L / 2 ≤ |L * ξ - u| := by
      have h4 : |L * ξ| - |u| ≤ |L * ξ - u| := abs_sub_abs_le_abs_sub _ _
      rw [abs_mul, abs_of_pos hL] at h4
      nlinarith
    rw [hsupp _ this]
    simp
  · rw [hsupp u (not_lt.mp hu)]
    simp
