-- Prove2me | solution 1 for Zeta23.Taper.integrable_re_paperFT_sq_and
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T01:47:24.199455+00:00
-- url     : https://prove2.me/submissions/4148e3b4-b80b-43e7-92cd-57d75e7dc3ad

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
import Theorems.Thm_Zeta23_Taper_contDiff_paperFT_ofReal
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






theorem hasCompactSupport_of_support_subset_abs {E : Type*} [Zero E] {f : ℝ → E} {Λ : ℝ}
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ) : HasCompactSupport f := by
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -Λ) (b := Λ)) ?_
  intro u hu
  exact abs_le.mp (hsupp u hu)




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




namespace Taper

/-! ## Generic facts about the paper-convention transform `h_v(z) = ∫ v(u) e^{izu} du` of a REAL
function `v`.  Everything in the [eq:PhigA] sentence is an instance of these with `v = φ` or `v = φ²`. -/

section Generic

variable {v : ℝ → ℝ}





theorem contDiff_re_paperFT_ofReal {f : ℝ → ℂ} (hf : Continuous f) (hs : HasCompactSupport f)
    (n : ℕ∞) : ContDiff ℝ n (fun r : ℝ => (paperFT f r).re) :=
  Complex.reCLM.contDiff.comp (contDiff_paperFT_ofReal hf hs n)

/-- A continuous `h : ℝ → ℝ` with `|h r| (1 + r²) ≤ K` is integrable (dominated by `K/(1+r²)`). -/
theorem integrable_of_abs_mul_one_add_sq_le {h : ℝ → ℝ} (hc : Continuous h) {K : ℝ}
    (hK : ∀ r, |h r| * (1 + r ^ 2) ≤ K) : Integrable h := by
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul K) hc.aestronglyMeasurable ?_
  refine Eventually.of_forall fun r => ?_
  have hpos : 0 < 1 + r ^ 2 := by positivity
  rw [Real.norm_eq_abs, ← div_eq_mul_inv, le_div_iff₀ hpos]
  exact hK r


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

theorem solution {f : ℝ → ℂ} {Λ : ℝ} (hf : ContDiff ℝ 2 f)
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ Λ) :
    Integrable (fun r : ℝ => (paperFT f r).re ^ 2) ∧
      Integrable (fun r : ℝ => (paperFT f r).re ^ 2 * |r|) := by
  have hcs : HasCompactSupport f := hasCompactSupport_of_support_subset_abs hsupp
  have hfi : Integrable f := hf.continuous.integrable_of_hasCompactSupport hcs
  set C₀ : ℝ := ∫ u, ‖f u‖
  set C₂ : ℝ := ∫ u, ‖deriv (deriv f) u‖
  set K : ℝ := C₀ + C₂
  -- pointwise decay at real points
  have hG : ∀ r : ℝ, ‖paperFT f r‖ ≤ C₀ := by
    intro r
    simpa using norm_paperFT_le hfi hsupp (r : ℂ)
  have hG2 : ∀ r : ℝ, ‖paperFT f r‖ * r ^ 2 ≤ C₂ := by
    intro r
    have := norm_paperFT_mul_sq_le hf hsupp (r : ℂ)
    simpa [sq_abs] using this
  have hGK : ∀ r : ℝ, ‖paperFT f r‖ * (1 + r ^ 2) ≤ K := by
    intro r
    have := hG r; have := hG2 r
    simp only [K]; nlinarith
  have hGr : ∀ r : ℝ, ‖paperFT f r‖ * |r| ≤ K := by
    intro r
    refine le_trans ?_ (hGK r)
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    nlinarith [abs_nonneg r, sq_abs r]
  have hre : ∀ r : ℝ, (paperFT f r).re ^ 2 ≤ ‖paperFT f r‖ ^ 2 := fun r =>
    sq_le_sq' (by linarith [abs_le.mp (Complex.abs_re_le_norm (paperFT f r))])
      (le_trans (le_abs_self _) (Complex.abs_re_le_norm _))
  have hC₀ : 0 ≤ C₀ := integral_nonneg fun _ => norm_nonneg _
  have hcont : Continuous fun r : ℝ => (paperFT f r).re :=
    (contDiff_re_paperFT_ofReal hf.continuous hcs 0).continuous
  constructor
  · apply integrable_of_abs_mul_one_add_sq_le (by fun_prop) (K := C₀ * K)
    intro r
    rw [abs_of_nonneg (sq_nonneg _)]
    calc (paperFT f r).re ^ 2 * (1 + r ^ 2)
        ≤ ‖paperFT f r‖ ^ 2 * (1 + r ^ 2) := mul_le_mul_of_nonneg_right (hre r) (by positivity)
      _ = ‖paperFT f r‖ * (‖paperFT f r‖ * (1 + r ^ 2)) := by ring
      _ ≤ C₀ * K := mul_le_mul (hG r) (hGK r) (by positivity) hC₀
  · apply integrable_of_abs_mul_one_add_sq_le (by fun_prop) (K := K * K)
    intro r
    rw [abs_of_nonneg (by positivity)]
    calc (paperFT f r).re ^ 2 * |r| * (1 + r ^ 2)
        ≤ ‖paperFT f r‖ ^ 2 * |r| * (1 + r ^ 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hre r) (abs_nonneg r))
            (by positivity)
      _ = (‖paperFT f r‖ * |r|) * (‖paperFT f r‖ * (1 + r ^ 2)) := by ring
      _ ≤ K * K := mul_le_mul (hGr r) (hGK r) (by positivity) (le_trans (by positivity) (hGr r))
