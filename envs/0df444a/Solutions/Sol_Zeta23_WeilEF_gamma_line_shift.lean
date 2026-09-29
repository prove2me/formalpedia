-- Prove2me | solution 1 for Zeta23.WeilEF.gamma_line_shift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T04:16:06.53229+00:00
-- url     : https://prove2.me/submissions/68d1f046-1885-479f-bbb3-499acaec03ef

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_ExplicitFormula
import Definitions.Def_Zeta23_GammaFacts_Series
import Definitions.Def_Zeta23_GammaFacts_StirlingVert
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_WeilEF_VerticalLine
import Theorems.Thm_Zeta23_WeilEF_differentiableAt_GammaR
import Theorems.Thm_Zeta23_WeilEF_differentiable_paperFT
import Theorems.Thm_Zeta23_WeilEF_log_two_add_div_le
import Theorems.Thm_Zeta23_WeilEF_norm_logDeriv_GammaR_le
import Theorems.Thm_Zeta23_WeilEF_norm_paperFT_le_uniform
import Theorems.Thm_Zeta23_WeilEF_vertical_line_shift

-- from Zeta23.ExplicitFormula.Bridge
section
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

/-- A compactly supported function on ℝ is supported in some `[−Λ, Λ]`. -/
theorem exists_abs_le_of_hasCompactSupport {k : ℝ → ℂ} (hkc : HasCompactSupport k) :
    ∃ Λ : ℝ, ∀ u, k u ≠ 0 → |u| ≤ Λ := by
  obtain ⟨R, hR⟩ := hkc.isCompact.isBounded.subset_closedBall 0
  refine ⟨R, fun u hu => ?_⟩
  have := hR (subset_tsupport _ (Function.mem_support.mpr hu))
  simpa [Real.norm_eq_abs] using this








end EF
end Zeta23
end
end

-- from Zeta23.WeilEF.XiLogDeriv
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/XiLogDeriv.lean
The completed zeta function Λ = completedRiemannZeta: log-derivative decomposition, functional equation
for logDeriv, zeros in the strip = nontrivial zeros of ζ with equal analytic order.

Mathlib normalization (verified): for s ≠ 0, riemannZeta s = completedRiemannZeta s / Gammaℝ s
(riemannZeta_def_of_ne_zero) and Gammaℝ s ≠ 0 for 0 < Re s (Gammaℝ_ne_zero_of_re_pos); hence on the
open right half-plane Λ = Γℝ · ζ on the nose (completedZeta_eventuallyEq_mul) — no pole bookkeeping is
needed for the three statements below (Λ's poles at 0, 1 are excluded by hypothesis).
-/

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex Filter Topology


/-- Γℝ is analytic at every point of the right half-plane. -/
lemma analyticAt_Gammaℝ {s : ℂ} (hs : 0 < s.re) : AnalyticAt ℂ Gammaℝ s := by
  have hopen : IsOpen {u : ℂ | 0 < u.re} := isOpen_lt continuous_const Complex.continuous_re
  exact DifferentiableOn.analyticAt (fun u hu => (differentiableAt_GammaR hu).differentiableWithinAt)
    (hopen.mem_nhds hs)






end WeilEF
end Zeta23
end
end

-- from Zeta23.WeilEF.VerticalLine
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/VerticalLine.lean.  Vertical-line integrals for the EF contour.

KEY DEVICE (no contour shifting needed on the prime side): for s = c + it on a vertical line,
H(s) := h((s−1/2)/i) = paperFT k (t − i·b) with b := c − 1/2, and
  paperFT k (t − i·b) = paperFT k_b t,  where k_b(u) := k(u)·e^{b·u}  (the TILTED test function,
still C_c²).  Hence the line integral (1/2π)∫ H(c+it)·n^{−c−it} dt is, by Fourier inversion of
k_b (Zeta23.EF.paper_inversion, proved in Zeta23/ExplicitFormula.lean, with integrability from
Zeta23/ExplicitFormula/Bridge.lean's integrable_fourier_of_contDiff_two),
  n^{−c}·k_b(log n) = n^{−c}·k(log n)·n^{b} = n^{−1/2}·k(log n).
Summing against −ζ'/ζ(c+it) = Σ Λ(n)n^{−c−it} (Mathlib LSeries, 1 < c) with a dominated
tsum/integral swap (domination: ‖paperFT k_b t‖(1+t²) ≤ ‖k_b‖₁+‖k_b''‖₁ from
Zeta23.EF.norm_paperFT_mul_one_add_sq_le × Σ Λ(n)n^{−c} < ∞) gives the prime side.
-/

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex MeasureTheory
open scoped ArithmeticFunction













/-- continuity ⇒ integrability on vertical lines under a majorant (used by vertical_line_shift). -/
lemma integrable_line {f : ℂ → ℂ} {σ : ℝ} (hf : ∀ t : ℝ, DifferentiableAt ℂ f (σ + t * I))
    {φ : ℝ → ℝ} (hφ : Integrable φ) (hb : ∀ t : ℝ, ‖f (σ + t * I)‖ ≤ φ t) :
    Integrable (fun t : ℝ => f (σ + t * I)) := by
  have hc : Continuous (fun t : ℝ => f (σ + t * I)) := by
    refine continuous_iff_continuousAt.mpr fun t => ?_
    have hg : Continuous (fun t : ℝ => (σ : ℂ) + t * I) := by fun_prop
    show ContinuousAt (f ∘ fun t : ℝ => (σ : ℂ) + t * I) t
    exact ContinuousAt.comp_of_eq (hf t).continuousAt hg.continuousAt rfl
  exact hφ.mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hb)








end WeilEF
end Zeta23
end
open Zeta23
open WeilEF
open Complex MeasureTheory
open scoped ArithmeticFunction

theorem solution {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k)
    {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3/2) :
    ∫ t : ℝ, (Hfn k (c + t * I) + Hfn k (1 - c - t * I)) * logDeriv Complex.Gammaℝ (c + t * I)
      = ∫ t : ℝ, paperFT k t
        * (logDeriv Complex.Gammaℝ (1/2 + t * I) + logDeriv Complex.Gammaℝ (1/2 - t * I)) := by
  set G := logDeriv Complex.Gammaℝ with hG
  -- differentiability
  have hHd : Differentiable ℂ (Hfn k) := by
    have h := differentiable_paperFT hk.continuous hkc
    show Differentiable ℂ (fun s => paperFT k ((s - 1/2) / I))
    exact h.comp ((differentiable_id.sub_const _).div_const I)
  have hGd : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ G s := by
    intro s hs
    have hA := analyticAt_Gammaℝ hs
    have : G = fun z => deriv Gammaℝ z / Gammaℝ z := by funext z; rw [hG, logDeriv_apply]
    rw [this]
    exact hA.deriv.differentiableAt.div hA.differentiableAt (Gammaℝ_ne_zero_of_re_pos hs)
  set f₁ : ℂ → ℂ := fun s => Hfn k s * G s with hf₁
  set f₂ : ℂ → ℂ := fun s => Hfn k (1 - s) * G s with hf₂
  have hf₁d : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ c → DifferentiableAt ℂ f₁ s := fun s h1 _ =>
    (hHd s).mul (hGd s (by linarith))
  have hf₂d : ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ c → DifferentiableAt ℂ f₂ s := fun s h1 _ =>
    ((hHd (1 - s)).comp s ((differentiableAt_const _).sub differentiableAt_id)).mul (hGd s (by linarith))
  -- the majorant
  obtain ⟨Lam₁, hLam₁⟩ := Zeta23.EF.exists_abs_le_of_hasCompactSupport hkc
  set Lam : ℝ := max Lam₁ 0 with hLam
  have hLam0 : 0 ≤ Lam := le_max_right _ _
  have hsupp : ∀ u, k u ≠ 0 → |u| ≤ Lam := fun u hu => (hLam₁ u hu).trans (le_max_left _ _)
  have hki : Integrable k := hk.continuous.integrable_of_hasCompactSupport hkc
  set N : ℝ := (∫ u, ‖k u‖) + ∫ u, ‖deriv (deriv k) u‖ with hN
  have hN0 : 0 ≤ N := add_nonneg (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)
  obtain ⟨CG, hCG, hGb⟩ := norm_logDeriv_GammaR_le
  set M : ℝ := 2 * Real.exp Lam * N * CG * 6 with hM
  have hM0 : 0 ≤ M := by positivity
  set φ : ℝ → ℝ := fun t => M * (1 + ‖t‖) ^ (-(3 / 2 : ℝ)) with hφ
  have hφi : Integrable φ := by
    have := (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 3/2)
      (by rw [Module.finrank_self]; norm_num)).const_mul M
    exact this
  have hφlim : Filter.Tendsto (fun x : ℝ => M * (1 + x) ^ (-(3 / 2 : ℝ))) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun x : ℝ => (1 + x) ^ (-(3 / 2 : ℝ))) Filter.atTop (nhds 0) :=
      (tendsto_rpow_neg_atTop (by norm_num)).comp (Filter.tendsto_atTop_add_const_left _ 1 Filter.tendsto_id)
    simpa using h1.const_mul M
  have hφtop : Filter.Tendsto φ Filter.atTop (nhds 0) := by
    have : φ = (fun x : ℝ => M * (1 + x) ^ (-(3 / 2 : ℝ))) ∘ (fun t : ℝ => ‖t‖) := by
      funext t; simp [hφ]
    rw [this]
    exact hφlim.comp (by simpa using Filter.tendsto_abs_atTop_atTop)
  have hφbot : Filter.Tendsto φ Filter.atBot (nhds 0) := by
    have : φ = (fun x : ℝ => M * (1 + x) ^ (-(3 / 2 : ℝ))) ∘ (fun t : ℝ => ‖t‖) := by
      funext t; simp [hφ]
    rw [this]
    exact hφlim.comp (by simpa using Filter.tendsto_abs_atBot_atTop)
  -- the key pointwise bound: for |Im z| ≤ 1, ‖paperFT k z‖·‖G(σ+it)‖ ≤ φ t when Re z = ±t
  have hkey : ∀ (σ t : ℝ) (z : ℂ), 1 / 2 ≤ σ → σ ≤ c → |z.im| ≤ 1 → z.re ^ 2 = t ^ 2 →
      ‖paperFT k z‖ * ‖G (σ + t * I)‖ ≤ φ t := by
    intro σ t z h1 h2 hz hzt
    have hH := norm_paperFT_le_uniform hk hki hLam0 hsupp hz
    rw [hzt] at hH
    have hGG := hGb σ t h1 (by linarith)
    have hl := log_two_add_div_le (abs_nonneg t)
    calc ‖paperFT k z‖ * ‖G (σ + t * I)‖
        ≤ (2 * Real.exp Lam * N / (1 + t ^ 2)) * (CG * Real.log (2 + |t|)) :=
          mul_le_mul hH hGG (norm_nonneg _) (by positivity)
      _ = (2 * Real.exp Lam * N * CG) * (Real.log (2 + |t|) / (1 + |t| ^ 2)) := by
          rw [sq_abs]; ring
      _ ≤ (2 * Real.exp Lam * N * CG) * (6 * (1 + |t|) ^ (-(3 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hl (by positivity)
      _ = φ t := by simp only [hφ, hM, Real.norm_eq_abs]; ring
  -- z-bookkeeping for Hfn on the two lines
  have hz₁ : ∀ σ t : ℝ, ((σ : ℂ) + t * I - 1 / 2) / I = (t : ℂ) + ((1 / 2 - σ : ℝ) : ℂ) * I := by
    intro σ t; field_simp; push_cast; ring_nf; simp [I_sq]; ring
  have hz₂ : ∀ σ t : ℝ, ((1 - ((σ : ℂ) + t * I)) - 1 / 2) / I = ((-t : ℝ) : ℂ) + ((σ - 1 / 2 : ℝ) : ℂ) * I := by
    intro σ t; field_simp; push_cast; ring_nf; simp [I_sq]; ring
  have hb₁ : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ c → ‖f₁ (σ + t * I)‖ ≤ φ t := by
    intro σ t h1 h2
    simp only [hf₁, Hfn, norm_mul]
    rw [hz₁]
    refine hkey σ t _ h1 h2 ?_ ?_
    · simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one, zero_add, add_zero]
      rw [abs_le]; constructor <;> linarith
    · simp
  have hb₂ : ∀ σ t : ℝ, 1 / 2 ≤ σ → σ ≤ c → ‖f₂ (σ + t * I)‖ ≤ φ t := by
    intro σ t h1 h2
    simp only [hf₂, Hfn, norm_mul]
    rw [hz₂]
    refine hkey σ t _ h1 h2 ?_ ?_
    · simp only [add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one, zero_add, add_zero]
      rw [abs_le]; constructor <;> linarith
    · simp
  -- shift both lines
  have hab : (1:ℝ) / 2 ≤ c := by linarith
  have hs₁ := vertical_line_shift hab hf₁d hφi hb₁ hφtop hφbot
  have hs₂ := vertical_line_shift hab hf₂d hφi hb₂ hφtop hφbot
  -- integrability on the lines
  have hi₁c : Integrable (fun t : ℝ => f₁ (c + t * I)) :=
    integrable_line (fun t => hf₁d _ (by simp; linarith) (by simp)) hφi (fun t => hb₁ c t hab le_rfl)
  have hi₂c : Integrable (fun t : ℝ => f₂ (c + t * I)) :=
    integrable_line (fun t => hf₂d _ (by simp; linarith) (by simp)) hφi (fun t => hb₂ c t hab le_rfl)
  have hi₁h : Integrable (fun t : ℝ => f₁ ((1/2 : ℝ) + t * I)) :=
    integrable_line (fun t => hf₁d _ (by simp) (by simp; linarith)) hφi (fun t => hb₁ (1/2) t le_rfl hab)
  have hi₂h : Integrable (fun t : ℝ => f₂ ((1/2 : ℝ) + t * I)) :=
    integrable_line (fun t => hf₂d _ (by simp) (by simp; linarith)) hφi (fun t => hb₂ (1/2) t le_rfl hab)
  -- LHS = ∫ f₁(c+it) + ∫ f₂(c+it)
  have hL : ∫ t : ℝ, (Hfn k (c + t * I) + Hfn k (1 - c - t * I)) * G (c + t * I)
      = (∫ t : ℝ, f₁ (c + t * I)) + ∫ t : ℝ, f₂ (c + t * I) := by
    rw [← integral_add hi₁c hi₂c]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [hf₁, hf₂]
    rw [show (1 : ℂ) - (↑c + ↑t * I) = 1 - ↑c - ↑t * I by ring]
    ring
  rw [hL, hs₁, hs₂]
  -- evaluate on the critical line
  have e₁ : ∀ t : ℝ, f₁ ((1/2 : ℝ) + t * I) = paperFT k t * G (1/2 + t * I) := by
    intro t
    simp only [hf₁, Hfn]
    congr 2
    · push_cast; field_simp; ring
    · push_cast; ring
  have e₂ : ∀ t : ℝ, f₂ ((1/2 : ℝ) + t * I) = paperFT k (((-t : ℝ) : ℂ)) * G (1/2 + t * I) := by
    intro t
    simp only [hf₂, Hfn]
    congr 2
    · push_cast; field_simp; ring
    · push_cast; ring
  simp_rw [e₁, e₂]
  -- t ↦ −t in the second integral
  have hneg : ∫ t : ℝ, paperFT k (((-t : ℝ) : ℂ)) * G (1/2 + t * I)
      = ∫ t : ℝ, paperFT k t * G (1/2 - t * I) := by
    rw [← integral_neg_eq_self]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [neg_neg]
    push_cast
    ring_nf
  rw [hneg, ← integral_add]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    ring
  · have := hi₁h; simp_rw [e₁] at this; exact this
  · have := hi₂h; simp_rw [e₂] at this
    have h2 := this.comp_neg
    simp only [neg_neg] at h2
    refine (h2.congr (Filter.Eventually.of_forall fun t => ?_))
    push_cast; ring_nf
