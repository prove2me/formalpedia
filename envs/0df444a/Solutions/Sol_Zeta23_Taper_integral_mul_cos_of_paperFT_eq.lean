-- Prove2me | solution 1 for Zeta23.Taper.integral_mul_cos_of_paperFT_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T01:45:56.98315+00:00
-- url     : https://prove2.me/submissions/db7c11b2-e449-4bb3-a270-df9f44defa6e

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Taper_Basic
import Theorems.Thm_Zeta23_paperFT_ofReal_eq_fourier

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

theorem paperFT_def (f : ℝ → ℂ) (z : ℂ) : paperFT f z = ∫ u : ℝ, f u * cexp (I * z * u) := rfl

/-! Mathlib's `integral_const_mul` / `integral_mul_const` are stated for a general `RCLike L`,
and their instance path (RCLike-derived `NormedAddCommGroup ℂ`) does not match the
directly-synthesized `Complex.instNormedAddCommGroup` under `rw`'s reducible unification.
These ℂ-specialized restatements (same proofs) rewrite reliably. -/




/-- Equivalent form of the dictionary: `𝓕 f w = h_f(-2π w)`. -/
theorem fourier_eq_paperFT (f : ℝ → ℂ) (w : ℝ) :
    𝓕 f w = paperFT f (-(2 * π * w)) := by
  have := paperFT_ofReal_eq_fourier f (-(2 * π * w))
  push_cast at this ⊢
  rw [this]
  field_simp

/-! ### [eq:hfbound]

"`|h_f(x+iy)| ≤ e^{|y|Λ_f} min(‖f‖₁, ‖f''‖₁ |x+iy|⁻²)`, `supp f ⊂ [−Λ_f, Λ_f]`, by two integrations
by parts (`h_f(z) = (iz)⁻² ∫ f''(u) e^{izu} du` and `|e^{izu}| = e^{−yu} ≤ e^{|y|Λ_f}` on
`supp f`)."  We prove the two bounds separately, in multiplied-out form. -/










end Zeta23
end

-- from Zeta23.Taper.Fourier
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — Taper/Fourier.lean  (Fourier-side facts about the taper).
Canonical text: the paper, §2.2 [subsec:family]:
  "Thus φ̂ and Φ are real, even, entire; φ̂(0) ≤ L, Φ(0) = aL; φ̂² = Â_φ and Φ² = ĝ on ℝ;
   ∫_ℝ Φ² = 2π g(0) = 2π bL; g and A_φ are even".
Conventions: generic parameters (ϱ : ℝ → ℝ) (L w : ℝ); paper's
side condition is 1 ≤ w ≤ L/8 [eq:wrange]; each lemma carries the minimal hypothesis it needs.
The decay needed for integrability is taken directly
from Zeta23/Poisson/PaperFT.lean (norm_paperFT_le, norm_paperFT_mul_sq_le).

MATHLIB INVENTORY, what this file leans on:
* dictionary  Zeta23.paperFT_ofReal_eq_fourier : paperFT f s = 𝓕 f (-s/(2π))  (PaperFT.lean);
* convolution theorem  Real.fourier_mul_convolution_eq  (Mathlib/Analysis/Fourier/Convolution.lean)
  for integrable + continuous f₁ f₂ : ℝ → ℂ, 𝓕 (f₁ ⋆[mul ℂ ℂ] f₂) = 𝓕 f₁ · 𝓕 f₂ — the paper's
  autocorrelation (v ⋆ v)(y) = ∫ v(u) v(u+y) du coincides with Mathlib's convolution for EVEN v;
* Fourier inversion  MeasureTheory.Integrable.fourierInv_fourier_eq  (Mathlib/Analysis/Fourier/
  Inversion.lean): f, 𝓕 f integrable, f continuous at v ⇒ 𝓕⁻ (𝓕 f) v = f v.  "Plancherel"
  ∫ φ̂² = 2π ∫ φ² is obtained as inversion of Â_φ = φ̂² at 0 (no L² theory needed);
* smoothness  Real.contDiff_fourier  (Mathlib/Analysis/Fourier/FourierTransformDeriv.lean);
* integrable_inv_one_add_sq  (dominating function (1+r²)⁻¹ for the decay |φ̂(r)| ≤ min(C₀, C₂/r²)).
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform ComplexConjugate

namespace Zeta23

/-! ### ℂ-specialized restatements of RCLike-generic integral lemmas
(same workaround as `integral_const_mul_C` in PaperFT.lean: `rw` with the
RCLike-stated lemma can fail to unify the `NormedAddCommGroup ℂ` instance path). -/



theorem integral_re_C {f : ℝ → ℂ} (hf : Integrable f) : ∫ x, (f x).re = (∫ x, f x).re :=
  integral_re hf

namespace Taper

/-! ## Generic facts about the paper-convention transform `h_v(z) = ∫ v(u) e^{izu} du` of a REAL
function `v`.  Everything in the [eq:PhigA] sentence is an instance of these with `v = φ` or `v = φ²`. -/

section Generic

variable {v : ℝ → ℝ}








/-! ### The paper's autocorrelation `(v ⋆ v)(y) := ∫ v(u) v(u+y) du` [eq:PhigA] versus Mathlib's convolution -/






/-! ## Fourier inversion in the paper's convention, cosine form -/


end Generic

/-! ## "`φ̂` and `Φ` are real, even, entire; …" (facts stated after [eq:PhigA]) -/

section PhigA
variable {ϱ : ℝ → ℝ} {L w : ℝ}

/-! #### auxiliary packaging of φ and φ² as inputs to the generic lemmas -/











/-! #### real / even / conjugation symmetry (hypothesis-free: only "φ real and even" is used) -/






/-! #### continuity / differentiability on ℝ ("entire" is more than any consumer needs) -/




/-! #### values at 0 -/






/-! #### "`φ̂² = Â_φ` and `Φ² = ĝ` on ℝ" — convolution theorem -/



/-! #### integrability of `φ̂², φ̂²|r|, Φ², Φ²|r|` (decay [eq:hfbound] via PaperFT.lean) -/





/-! #### Plancherel / inversion identities -/





end PhigA

end Taper

end Zeta23
open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform ComplexConjugate
open Zeta23
open Taper
variable {v : ℝ → ℝ}

theorem solution {A G : ℝ → ℝ} (hA : Continuous A) (hAi : Integrable A)
    (hG : Integrable G) (hFT : ∀ r : ℝ, paperFT (fun u => (A u : ℂ)) r = (G r : ℂ)) (y : ℝ) :
    ∫ r, G r * Real.cos (r * y) = 2 * π * A y := by
  have hπ : (0 : ℝ) < 2 * π := by positivity
  set Ac : ℝ → ℂ := fun u => (A u : ℂ) with hAc
  have hF' : ∀ ξ : ℝ, 𝓕 Ac ξ = (G (-(2 * π) * ξ) : ℂ) := by
    intro ξ
    rw [fourier_eq_paperFT, ← hFT]
    congr 1
    push_cast
    ring
  have hF : 𝓕 Ac = fun ξ : ℝ => (G (-(2 * π) * ξ) : ℂ) := funext hF'
  have hFi : Integrable (𝓕 Ac) := by
    rw [hF]
    exact (hG.comp_mul_left' (by linarith : -(2 * π) ≠ 0)).ofReal
  have e1 : 𝓕⁻ (𝓕 Ac) y = Ac y :=
    hAi.ofReal.fourierInv_fourier_eq hFi (Complex.continuous_ofReal.comp hA).continuousAt
  set g : ℝ → ℂ := fun r => (G r : ℂ) * cexp ((-(y * r) : ℝ) * I) with hg
  have hgc : Continuous fun r : ℝ => cexp ((-(y * r) : ℝ) * I) := by fun_prop
  have hgi : Integrable g := by
    refine (hG.ofReal (𝕜 := ℂ)).norm.mono'
      ((hG.ofReal (𝕜 := ℂ)).aestronglyMeasurable.mul hgc.aestronglyMeasurable)
      (Eventually.of_forall fun r => ?_)
    simp only [hg, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
    exact le_rfl
  have e2 : 𝓕⁻ (𝓕 Ac) y = ∫ ξ, g (-(2 * π) * ξ) := by
    rw [fourierInv_eq_fourier_neg, fourier_eq_paperFT, paperFT_def]
    congr 1 with ξ
    rw [hF']
    simp only [hg]
    congr 2
    push_cast
    ring
  have e3 : (∫ r, g r).re = ∫ r, G r * Real.cos (r * y) := by
    rw [← integral_re_C hgi]
    congr 1 with r
    simp only [hg, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Real.cos_neg, mul_comm y r]
  have habs : |(-(2 * π))⁻¹| = (2 * π)⁻¹ := by
    rw [abs_inv, abs_neg, abs_of_pos hπ]
  have e2b : (∫ ξ, g (-(2 * π) * ξ)) = ((2 * π)⁻¹ : ℝ) • ∫ r, g r := by
    have := Measure.integral_comp_mul_left g (-(2 * π))
    rw [habs] at this
    exact this
  have e4 : A y = (2 * π)⁻¹ * ∫ r, G r * Real.cos (r * y) := by
    have := congrArg Complex.re (e1.symm.trans (e2.trans e2b))
    rw [Complex.smul_re, smul_eq_mul, e3] at this
    simpa [hAc] using this
  rw [e4, ← mul_assoc, mul_inv_cancel₀ hπ.ne', one_mul]
