-- Prove2me | solution 1 for Zeta23.WeilEF.norm_paperFT_le_uniform
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T04:17:15.14027+00:00
-- url     : https://prove2.me/submissions/0a77c9ec-8c39-49f3-9939-017337e1da57

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
import Theorems.Thm_Zeta23_norm_paperFT_le
import Theorems.Thm_Zeta23_norm_paperFT_mul_sq_le

-- from Zeta23.Poisson.PaperFT
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
The paper's Fourier convention and the bound [eq:hfbound].

Reference: the paper, §2.1 [subsec:weil].
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform

namespace Zeta23

/-! `Zeta23.paperFT (f : ℝ → ℂ) (z : ℂ) : ℂ := ∫ u, f u * cexp (I * z * u)` is defined in
`Zeta23/Defs.lean`: the paper's convention [subsec:weil] "h_f(z) := f̂(z) = ∫ f(u) e^{izu} du",
sign `+i`, no `2π`, complex argument.  This file supplies the dictionary to Mathlib's `𝓕`
(`∫ f(v) e^{-2πi v w} dv`) and the decay bound [eq:hfbound]. -/


/-! Mathlib's `integral_const_mul` / `integral_mul_const` are stated for a general `RCLike L`,
and their instance path (RCLike-derived `NormedAddCommGroup ℂ`) does not match the
directly-synthesized `Complex.instNormedAddCommGroup` under `rw`'s reducible unification.
These ℂ-specialized restatements (same proofs) rewrite reliably. -/





/-! ### [eq:hfbound]

"`|h_f(x+iy)| ≤ e^{|y|Λ_f} min(‖f‖₁, ‖f''‖₁ |x+iy|⁻²)`, `supp f ⊂ [−Λ_f, Λ_f]`, by two integrations
by parts (`h_f(z) = (iz)⁻² ∫ f''(u) e^{izu} du` and `|e^{izu}| = e^{−yu} ≤ e^{|y|Λ_f}` on
`supp f`)."  We prove the two bounds separately, in multiplied-out form. -/









/-- [eq:hfbound] in the paper's form for `z ≠ 0`: `‖h_f(z)‖ ≤ e^{|Im z|Λ} ‖f''‖₁ / ‖z‖²`. -/
theorem norm_paperFT_le_div {f : ℝ → ℂ} {Λ : ℝ} (hf : ContDiff ℝ 2 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ) {z : ℂ} (hz : z ≠ 0) :
    ‖paperFT f z‖ ≤ Real.exp (|z.im| * Λ) * (∫ u, ‖deriv (deriv f) u‖) / ‖z‖ ^ 2 := by
  rw [le_div_iff₀ (by positivity)]
  exact norm_paperFT_mul_sq_le hf hsupp z

end Zeta23
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





















end WeilEF
end Zeta23
end
open Zeta23
open WeilEF
open Complex MeasureTheory
open scoped ArithmeticFunction

theorem solution {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hki : Integrable k) {Lam : ℝ}
    (hLam : 0 ≤ Lam) (hsupp : ∀ u, k u ≠ 0 → |u| ≤ Lam) {z : ℂ} (hz : |z.im| ≤ 1) :
    ‖paperFT k z‖ ≤ 2 * Real.exp Lam * ((∫ u, ‖k u‖) + ∫ u, ‖deriv (deriv k) u‖) / (1 + z.re ^ 2) := by
  set N₀ := ∫ u, ‖k u‖ with hN₀
  set N₂ := ∫ u, ‖deriv (deriv k) u‖ with hN₂
  have hN₀0 : 0 ≤ N₀ := integral_nonneg fun _ => norm_nonneg _
  have hN₂0 : 0 ≤ N₂ := integral_nonneg fun _ => norm_nonneg _
  have he : Real.exp (|z.im| * Lam) ≤ Real.exp Lam := Real.exp_le_exp.mpr (by nlinarith [abs_nonneg z.im])
  by_cases hre : z.re ^ 2 ≤ 1
  · have b0 := norm_paperFT_le hki hsupp z
    calc ‖paperFT k z‖ ≤ Real.exp (|z.im| * Lam) * N₀ := b0
      _ ≤ Real.exp Lam * N₀ := mul_le_mul_of_nonneg_right he hN₀0
      _ ≤ 2 * Real.exp Lam * (N₀ + N₂) / (1 + z.re ^ 2) := by
          rw [le_div_iff₀ (by positivity)]
          have := Real.exp_pos Lam
          nlinarith [mul_nonneg this.le hN₂0, mul_nonneg this.le hN₀0]
  · push Not at hre
    have hz0 : z ≠ 0 := fun h => by rw [h] at hre; simp at hre; linarith
    have b2 := norm_paperFT_le_div hk hsupp hz0
    have hzn : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; nlinarith [sq_nonneg z.im]
    have hzpos : 0 < ‖z‖ ^ 2 := by linarith
    calc ‖paperFT k z‖ ≤ Real.exp (|z.im| * Lam) * N₂ / ‖z‖ ^ 2 := b2
      _ ≤ Real.exp Lam * N₂ / z.re ^ 2 := by
          gcongr
      _ ≤ 2 * Real.exp Lam * (N₀ + N₂) / (1 + z.re ^ 2) := by
          rw [div_le_div_iff₀ (by linarith) (by positivity)]
          have := Real.exp_pos Lam
          nlinarith [mul_nonneg this.le hN₂0, mul_nonneg this.le hN₀0]
