-- Prove2me | solution 1 for Zeta23.Taper.ofReal_autocorr_eq_convolution
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T01:43:57.850189+00:00
-- url     : https://prove2.me/submissions/35548ff1-49fa-439f-b1a8-c8f9319d9054

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

theorem integral_ofReal_C (f : ℝ → ℝ) : ∫ x, (f x : ℂ) = ((∫ x, f x : ℝ) : ℂ) := integral_ofReal



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

theorem solution (hv : ∀ u, v (-u) = v u) :
    (fun y => (Params.autocorr v y : ℂ)) =
      convolution (fun u => (v u : ℂ)) (fun u => (v u : ℂ)) (ContinuousLinearMap.mul ℂ ℂ)
        volume := by
  funext y
  rw [convolution_def, Params.autocorr, ← integral_ofReal_C, ← integral_neg_eq_self]
  congr 1 with t
  rw [hv, ContinuousLinearMap.mul_apply', neg_add_eq_sub]
  push_cast
  ring
