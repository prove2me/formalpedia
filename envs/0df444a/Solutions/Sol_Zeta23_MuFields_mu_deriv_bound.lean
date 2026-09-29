-- Prove2me | solution 1 for Zeta23.MuFields.mu_deriv_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T07:13:43.614676+00:00
-- url     : https://prove2.me/submissions/be808223-881d-4a83-81b1-3b12a8a15f99

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
import Definitions.Def_Zeta23_GammaFacts_Series
import Theorems.Thm_Zeta23_MuFields_summable_quarter_line
import Theorems.Thm_Zeta23_MuFields_trigamma_tail_le
import Theorems.Thm_Zeta23_Stirling_differentiableAt_digamma
import Theorems.Thm_Zeta23_Stirling_hasSum_trigamma

-- from Zeta23.GammaFacts.Mu
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

/-- Points a + it with a ∈ (0,1) avoid the integers. -/
lemma abscissa_mem (ha0 : 0 < a) (ha1 : a < 1) (t : ℝ) :
    ((a : ℂ) + Complex.I * (t : ℂ)) ∈ Complex.integerComplement := by
  rintro ⟨k, hk⟩
  have hre := congrArg Complex.re hk
  simp at hre
  have h0 : (0 : ℤ) < k := by
    have h : (0 : ℝ) < (k : ℝ) := by rw [hre]; exact ha0
    exact_mod_cast h
  have h1 : k < 1 := by
    have h : (k : ℝ) < 1 := by rw [hre]; exact ha1
    exact_mod_cast h
  omega





/-! ### Monotonicity on the vertical line, and the μ order facts -/






/-! ### The derivative bound μ′ ≪ 1/|τ|  (via the trigamma series) -/




end MuFields
end Zeta23
end
open Zeta23
open MuFields
open Complex Filter Topology
variable {a : ℝ}
set_option backward.isDefEq.respectTransparency false

theorem solution : ∃ C : ℝ, ∀ τ : ℝ, 1 ≤ |τ| → |deriv Zeta23.mu τ| ≤ C / |τ| := by
  refine ⟨24 / Real.pi, fun τ hτ => ?_⟩
  have hτ0 : (0 : ℝ) < |τ| := by linarith
  set zA : ℂ := (1 / 4 : ℂ) + (Complex.I / 2) * (τ : ℂ) with hzA
  have hzA_eq : zA = ((1 / 4 : ℝ) : ℂ) + Complex.I * ((τ / 2 : ℝ) : ℂ) := by
    rw [hzA]
    push_cast
    ring
  have hmem : zA ∈ Complex.integerComplement := by
    rw [hzA_eq]
    exact abscissa_mem (by norm_num) (by norm_num) (τ / 2)
  have hψd : DifferentiableAt ℂ Complex.digamma zA :=
    Zeta23.Stirling.differentiableAt_digamma hmem
  -- chain rule: μ has derivative (1/2π)·Re(ψ′(zA)·(I/2)) at τ
  have hginner : HasDerivAt (fun x : ℝ => (1 / 4 : ℂ) + (Complex.I / 2) * (x : ℂ))
      (Complex.I / 2) τ := by
    have h1 : HasDerivAt (fun x : ℝ => ((x : ℝ) : ℂ)) 1 τ := Complex.ofRealCLM.hasDerivAt
    have h2 := (h1.const_mul (Complex.I / 2)).const_add ((1 / 4 : ℂ))
    simpa using h2
  have hcompd : HasDerivAt
      (fun x : ℝ => Complex.digamma ((1 / 4 : ℂ) + (Complex.I / 2) * (x : ℂ)))
      ((Complex.I / 2) • deriv Complex.digamma zA) τ := by
    have h3 := HasDerivAt.scomp τ hψd.hasDerivAt hginner
    exact h3
  have hre : HasDerivAt
      (fun x : ℝ => (Complex.digamma ((1 / 4 : ℂ) + (Complex.I / 2) * (x : ℂ))).re)
      (((Complex.I / 2) • deriv Complex.digamma zA).re) τ :=
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt τ hcompd)
  have hmuD : HasDerivAt Zeta23.mu
      (1 / (2 * Real.pi) * (((Complex.I / 2) • deriv Complex.digamma zA).re)) τ := by
    have h4 := (hre.const_mul (1 / (2 * Real.pi))).sub_const (Real.log Real.pi / (2 * Real.pi))
    have h5 : Zeta23.mu = fun x : ℝ =>
        1 / (2 * Real.pi) * (Complex.digamma ((1 / 4 : ℂ) + (Complex.I / 2) * (x : ℂ))).re
          - Real.log Real.pi / (2 * Real.pi) := by
      funext x
      unfold Zeta23.mu
      rw [show ((1 / 4 : ℂ) + Complex.I * (x : ℂ) / 2)
          = (1 / 4 : ℂ) + (Complex.I / 2) * (x : ℂ) from by ring]
    rw [h5]
    exact h4
  rw [hmuD.deriv]
  -- bound the derivative value by the trigamma tail
  have htri := Zeta23.Stirling.hasSum_trigamma hmem
  have hnorm_term : ∀ n : ℕ, ‖(1 : ℂ) / (zA + n) ^ 2‖
      = (((1 / 4 : ℝ) + n) ^ 2 + (τ / 2) ^ 2)⁻¹ := by
    intro n
    have hre2 : (zA + n).re = (1 / 4 : ℝ) + n := by
      rw [hzA_eq]
      simp
    have him2 : (zA + n).im = τ / 2 := by
      rw [hzA_eq]
      simp
    rw [norm_div, norm_one, norm_pow, one_div]
    congr 1
    rw [show ‖zA + (n : ℂ)‖ ^ 2 = Complex.normSq (zA + n) from Complex.sq_norm _,
      Complex.normSq_apply, hre2, him2]
    ring
  have hsummable_norm : Summable (fun n : ℕ => ‖(1 : ℂ) / (zA + n) ^ 2‖) := by
    refine (summable_quarter_line (τ / 2)).congr fun n => ?_
    exact (hnorm_term n).symm
  have hψ'bound : ‖deriv Complex.digamma zA‖ ≤ 24 / |τ| := by
    have h6 : deriv Complex.digamma zA = ∑' n : ℕ, (1 : ℂ) / (zA + n) ^ 2 := htri.tsum_eq.symm
    rw [h6]
    calc ‖∑' n : ℕ, (1 : ℂ) / (zA + n) ^ 2‖ ≤ ∑' n : ℕ, ‖(1 : ℂ) / (zA + n) ^ 2‖ :=
          norm_tsum_le_tsum_norm hsummable_norm
      _ = ∑' n : ℕ, (((1 / 4 : ℝ) + n) ^ 2 + (τ / 2) ^ 2)⁻¹ := by
          congr 1
          funext n
          exact hnorm_term n
      _ ≤ 12 / |τ / 2| := trigamma_tail_le (by
          rw [abs_div]
          rw [show |(2 : ℝ)| = 2 by norm_num]
          linarith)
      _ = 24 / |τ| := by
          rw [abs_div, show |(2 : ℝ)| = 2 by norm_num]
          field_simp
          norm_num
  -- |Re((I/2)•ψ′)| ≤ ‖ψ′‖/2
  have hval : |(((Complex.I / 2) • deriv Complex.digamma zA).re)|
      ≤ ‖deriv Complex.digamma zA‖ / 2 := by
    calc |(((Complex.I / 2) • deriv Complex.digamma zA).re)|
        ≤ ‖(Complex.I / 2) • deriv Complex.digamma zA‖ := Complex.abs_re_le_norm _
      _ = ‖Complex.I / 2‖ * ‖deriv Complex.digamma zA‖ := norm_smul _ _
      _ = ‖deriv Complex.digamma zA‖ / 2 := by
          rw [norm_div, Complex.norm_I]
          rw [show ‖(2 : ℂ)‖ = 2 from by
            rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, Complex.norm_real,
              Real.norm_eq_abs, abs_of_pos (by norm_num)]]
          ring
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (2 * Real.pi))]
  calc 1 / (2 * Real.pi) * |(((Complex.I / 2) • deriv Complex.digamma zA).re)|
      ≤ 1 / (2 * Real.pi) * (‖deriv Complex.digamma zA‖ / 2) := by
        gcongr
    _ ≤ 1 / (2 * Real.pi) * ((24 / |τ|) / 2) := by
        gcongr
    _ ≤ (24 / Real.pi) / |τ| := by
        rw [div_div, div_mul_eq_mul_div, one_mul]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        ring_nf
        have e1 : Real.pi * Real.pi⁻¹ = 1 := mul_inv_cancel₀ hπ.ne'
        have e2 : |τ| * |τ|⁻¹ = 1 := mul_inv_cancel₀ hτ0.ne'
        nlinarith [e1, e2]
