-- Prove2me | solution 1 for Zeta23.MuInts.int_mu_of_stirling
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T07:04:47.305335+00:00
-- url     : https://prove2.me/submissions/01caef78-e0b3-4a8e-b584-49c77755aab6

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
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_GammaFacts_IntMu
import Definitions.Def_Zeta23_GammaFacts_Series
import Theorems.Thm_Zeta23_MuInts_integral_main_eq
import Theorems.Thm_Zeta23_mu_smooth

-- from Zeta23.GammaFacts.IntMu
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/GammaFacts/IntMu.lean — the [eq:muints] Γ-half integrals.
Paper: "∫_T^{2T} μ(τ)dτ = Tℓ₁/(2π) + O(1/T)", "∫_T^{2T} μ(τ)² dτ = (Tℓ₁²/4π²)(1 + O(l⁻²))",
via "(eq:muints) follows from (eq:mufacts) … and ∫_T^{2T} log²(τ/2π) dτ = T(ℓ₁² + 1 − 2log²2)".
Both theorems take the Stirling field as a hypothesis (hst); the Stirling asymptotic itself is
proved elsewhere in the repository, so GammaFacts assembles with no Γ-hypothesis beyond it.
-/

noncomputable section

namespace Zeta23
namespace MuInts

open MeasureTheory intervalIntegral






end MuInts
end Zeta23
end
open Zeta23
open MuInts
open MeasureTheory intervalIntegral

theorem solution (hst : StirlingHyp) :
    ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      |(∫ τ in T..(2 * T), Zeta23.mu τ) - T * ell1 T / (2 * Real.pi)| ≤ C / T := by
  obtain ⟨C, hC⟩ := hst
  have hC0 : 0 ≤ C := by
    have h := hC 1 (by norm_num)
    have := abs_nonneg (Zeta23.mu 1 - 1 / (2 * Real.pi) * Real.log (|1| / (2 * Real.pi)))
    nlinarith
  have hμcont : Continuous Zeta23.mu := Zeta23.mu_smooth.continuous
  refine ⟨C, 1, fun T hT => ?_⟩
  have hT0 : (0 : ℝ) < T := by linarith
  -- split μ = main + error on [T, 2T]
  have hint_mu : IntervalIntegrable Zeta23.mu volume T (2 * T) :=
    hμcont.intervalIntegrable _ _
  have hint_main : IntervalIntegrable
      (fun τ : ℝ => (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) volume T (2 * T) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    refine ContinuousOn.mul continuousOn_const ?_
    intro τ hτ
    have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le hT0 hτ.1
    exact ((Real.continuousAt_log (by positivity)).comp
      (continuousAt_id.div_const _)).continuousWithinAt
  have hsplit : (∫ τ in T..(2 * T), Zeta23.mu τ)
      = (∫ τ in T..(2 * T), (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi)))
        + ∫ τ in T..(2 * T),
            (Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))) := by
    rw [← intervalIntegral.integral_add hint_main (hint_mu.sub hint_main)]
    congr 1
    funext τ
    ring
  rw [hsplit, integral_main_eq hT0]
  rw [add_sub_cancel_left]
  -- bound the error integral
  have herr_int : IntervalIntegrable
      (fun τ : ℝ => Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi)))
      volume T (2 * T) := hint_mu.sub hint_main
  have hbound : ∀ τ ∈ Set.Icc T (2 * T),
      |Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))| ≤ C / τ ^ 2 := by
    intro τ hτ
    have hτ1 : (1 : ℝ) ≤ τ := le_trans hT hτ.1
    have habs : |τ| = τ := abs_of_pos (by linarith)
    have h := hC τ (by rwa [habs])
    rwa [habs] at h
  have hCtau : IntervalIntegrable (fun τ : ℝ => C / τ ^ 2) volume T (2 * T) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    intro τ hτ
    have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le hT0 hτ.1
    exact (continuousAt_const.div (continuousAt_pow _ _) (by positivity)).continuousWithinAt
  have hCint : ∫ τ in T..(2 * T), C / τ ^ 2 = C / (2 * T) := by
    have hftc2 : ∀ τ ∈ Set.uIcc T (2 * T),
        HasDerivAt (fun x : ℝ => -C / x) (C / τ ^ 2) τ := by
      intro τ hτ
      rw [Set.uIcc_of_le (by linarith)] at hτ
      have hτ0 : (0 : ℝ) < τ := lt_of_lt_of_le hT0 hτ.1
      have hinv : HasDerivAt (fun x : ℝ => x⁻¹) (-1 / τ ^ 2) τ := (hasDerivAt_id τ).inv hτ0.ne'
      have h1 := hinv.const_mul (-C)
      have h3 : (fun x : ℝ => -C * x⁻¹) = fun x : ℝ => -C / x := by
        funext x
        ring
      rw [h3] at h1
      have heq : C / τ ^ 2 = -C * (-1 / τ ^ 2) := by ring
      rw [heq]
      exact h1
    rw [integral_eq_sub_of_hasDerivAt hftc2 hCtau]
    field_simp
    ring
  calc |∫ τ in T..(2 * T),
        (Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi)))|
      ≤ ∫ τ in T..(2 * T),
          |Zeta23.mu τ - (1 / (2 * Real.pi)) * Real.log (τ / (2 * Real.pi))| :=
        intervalIntegral.abs_integral_le_integral_abs (by linarith)
    _ ≤ ∫ τ in T..(2 * T), C / τ ^ 2 := by
        refine intervalIntegral.integral_mono_on (by linarith) herr_int.abs hCtau ?_
        intro τ hτ
        exact hbound τ hτ
    _ = C / (2 * T) := hCint
    _ ≤ C / T := by
        have h2 : (0 : ℝ) < 2 * T := by linarith
        rw [div_le_div_iff₀ h2 hT0]
        nlinarith
