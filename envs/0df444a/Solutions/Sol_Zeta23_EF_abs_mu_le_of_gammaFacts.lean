-- Prove2me | solution 1 for Zeta23.EF.abs_mu_le_of_gammaFacts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T08:02:34.688146+00:00
-- url     : https://prove2.me/submissions/a2da1d35-a103-44b1-b4a0-d0df831ae9fc

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_ExplicitFormula
import Definitions.Def_Zeta23_Hypotheses

-- from Zeta23.ExplicitFormula.Bridge
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ExplicitFormula/Bridge.lean

The two "all integrals absolutely convergent" side-facts of App. A [app:EF]:
  * `integrable_fourier_of_contDiff_two` : k ∈ C_c²(ℝ) ⇒ 𝓕 k ∈ L¹(ℝ)   (from [eq:hfbound], Zeta23/Poisson/PaperFT.lean);
  * `integrable_paperFT_mul_mu`          : k ∈ C_c²(ℝ) ⇒ h_k · μ ∈ L¹(ℝ)  (from [eq:hfbound] + H-Γ [eq:mufacts]);
and the clean bridge
  * `explicitFormulaPaper_of_lit` : EF_lit Z → GammaFacts → ExplicitFormulaPaper Z,
i.e. the literature-form explicit formula [eq:EFstd] (plus the Stirling facts for μ that PaperInputs already
carries) implies the paper's [prop:EF]/[eq:EF] exactly as Hypotheses.lean states it.
-/

open MeasureTheory Complex Filter Set
open scoped Real FourierTransform ComplexConjugate

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Zeta23
namespace EF









end EF
end Zeta23
end
open MeasureTheory Complex Filter Set
open scoped Real FourierTransform ComplexConjugate
set_option backward.isDefEq.respectTransparency false
open Zeta23
open EF

theorem solution (hΓ : GammaFacts) :
    ∃ K₂ : ℝ, 0 ≤ K₂ ∧ ∀ τ : ℝ, |mu τ| ≤ K₂ * (1 + |τ|) ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC⟩ := hΓ.stirling
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hΓ.smooth.continuous.continuousOn (s := Icc (-1 : ℝ) 1))
  have hπ : 0 < 1 / (2 * π) := by positivity
  have hL0 : 0 ≤ (1 / (2 * π)) * |Real.log (2 * π)| := mul_nonneg hπ.le (abs_nonneg _)
  set K₂ : ℝ := max M 0 + |C| + (1 / (2 * π)) * |Real.log (2 * π)| + 1 / π with hK₂
  have hK₂nn : 0 ≤ K₂ := by
    have : 0 ≤ max M 0 := le_max_right _ _
    have : 0 ≤ 1 / π := by positivity
    positivity
  refine ⟨K₂, hK₂nn, fun τ => ?_⟩
  have hb1 : 1 ≤ (1 + |τ|) ^ (1 / 2 : ℝ) :=
    Real.one_le_rpow (by linarith [abs_nonneg τ]) (by norm_num)
  rcases le_or_gt |τ| 1 with hτ | hτ
  · -- |τ| ≤ 1: continuity bound
    have := hM τ (abs_le.mp hτ)
    rw [Real.norm_eq_abs] at this
    calc |mu τ| ≤ max M 0 := this.trans (le_max_left _ _)
      _ ≤ K₂ * 1 := by
        rw [mul_one, hK₂]
        have : 0 ≤ 1 / π := by positivity
        linarith [abs_nonneg C]
      _ ≤ K₂ * (1 + |τ|) ^ (1 / 2 : ℝ) := by gcongr
  · -- |τ| ≥ 1: Stirling
    have hτ1 : 1 ≤ |τ| := hτ.le
    have hst := hC τ hτ1
    have hsq : 1 ≤ τ ^ 2 := by rw [← sq_abs]; nlinarith
    have hCτ : C / τ ^ 2 ≤ |C| := by
      calc C / τ ^ 2 ≤ |C| / τ ^ 2 := by gcongr; exact le_abs_self C
        _ ≤ |C| := div_le_self (abs_nonneg C) hsq
    have hlog : |Real.log (|τ| / (2 * π))| ≤ Real.log |τ| + |Real.log (2 * π)| := by
      rw [Real.log_div (by positivity) (by positivity)]
      calc abs (Real.log |τ| - Real.log (2 * π))
          ≤ abs (Real.log |τ|) + |Real.log (2 * π)| := abs_sub _ _
        _ = Real.log |τ| + |Real.log (2 * π)| := by rw [abs_of_nonneg (Real.log_nonneg hτ1)]
    have hlog2 : Real.log |τ| ≤ 2 * (1 + |τ|) ^ (1 / 2 : ℝ) := by
      have := Real.log_le_rpow_div (abs_nonneg τ) (by norm_num : (0 : ℝ) < 1 / 2)
      have hmono : |τ| ^ (1 / 2 : ℝ) ≤ (1 + |τ|) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (abs_nonneg τ) (by linarith) (by norm_num)
      calc Real.log |τ| ≤ |τ| ^ (1 / 2 : ℝ) / (1 / 2) := this
        _ = 2 * |τ| ^ (1 / 2 : ℝ) := by ring
        _ ≤ 2 * (1 + |τ|) ^ (1 / 2 : ℝ) := by gcongr
    have hmu : |mu τ| ≤ |C| + (1 / (2 * π)) * (Real.log |τ| + |Real.log (2 * π)|) := by
      have htri : |mu τ| ≤ |mu τ - 1 / (2 * π) * Real.log (|τ| / (2 * π))|
          + |1 / (2 * π) * Real.log (|τ| / (2 * π))| := by
        have := abs_add_le (mu τ - 1 / (2 * π) * Real.log (|τ| / (2 * π)))
          (1 / (2 * π) * Real.log (|τ| / (2 * π)))
        rwa [sub_add_cancel] at this
      calc |mu τ| ≤ C / τ ^ 2 + |1 / (2 * π) * Real.log (|τ| / (2 * π))| := by linarith
        _ ≤ |C| + (1 / (2 * π)) * (Real.log |τ| + |Real.log (2 * π)|) := by
          rw [abs_mul, abs_of_pos hπ]
          gcongr
    set b := (1 + |τ|) ^ (1 / 2 : ℝ) with hb
    calc |mu τ| ≤ |C| + (1 / (2 * π)) * (Real.log |τ| + |Real.log (2 * π)|) := hmu
      _ ≤ |C| + (1 / (2 * π)) * (2 * b + |Real.log (2 * π)|) := by gcongr
      _ = (|C| + (1 / (2 * π)) * |Real.log (2 * π)|) * 1 + (1 / π) * b := by ring
      _ ≤ (|C| + (1 / (2 * π)) * |Real.log (2 * π)|) * b + (1 / π) * b := by gcongr
      _ = (|C| + (1 / (2 * π)) * |Real.log (2 * π)| + 1 / π) * b := by ring
      _ ≤ K₂ * b := by
        gcongr; rw [hK₂]; linarith [le_max_right M 0]
