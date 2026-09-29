-- Prove2me | solution 1 for Zeta23.Taper.phiSqC_supp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T01:40:17.539827+00:00
-- url     : https://prove2.me/submissions/4c4bc1ed-5fc3-418c-abc5-78c851815725

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

-- from Zeta23.Taper.Basic
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — Taper/Basic.lean.  Definitions of the test family
[subsec:family] for generic parameters (ϱ : ℝ → ℝ) (L w : ℝ), and the basic facts of the sentence
after [eq:phidef].  Bodies are literally those of Zeta23/Defs.lean so that
P.phi T = Taper.phi P.ϱ (P.L T) P.w etc. are rfl (bridges in Zeta23/Taper.lean).

Sub-file map (umbrella = Zeta23/Taper.lean):
  Basic   — defs, support/plateau/evenness/C³
  Norms   — [eq:phinorms], [eq:abdef], c_ϱ, C₁, smoothstep
  Strip   — [eq:hfbound] specialized to φ
  Decay   — [eq:gbounds], [eq:psidef], [eq:psiints]
  Fourier — φ̂, Φ real/even/continuous, [eq:PhigA] facts, Plancherel, [eq:Phi2FT]
  Zeta23/Taper.lean — umbrella + the consumer-facing `Params` layer
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform

namespace Zeta23




namespace Taper

/-! ### Constants depending only on ϱ  [eq:phinorms] -/






/-! ### The taper φ [eq:phidef], a, b [eq:abdef], Φ, g, A_φ [eq:PhigA], ψ [eq:psidef] -/

variable (ϱ : ℝ → ℝ) (L w : ℝ)











/-! ### Basic properties of φ (the sentence after [eq:phidef]):
"`φ ∈ C_c³(ℝ)` is even, `0 ≤ φ ≤ 1`, `supp φ = [−L/2, L/2]`, `φ = 1` on `[−L/2+w, L/2−w]`" -/

section Basic
variable {ϱ L w}




/-- `φ(u) = 0` for `|u| ≥ L/2`. -/
theorem phi_eq_zero (hϱ : TaperProfile ϱ) (hw : 0 < w) {u : ℝ} (hu : L / 2 ≤ |u|) :
    phi ϱ L w u = 0 := by
  unfold phi
  apply hϱ.eq_zero
  apply div_nonpos_of_nonpos_of_nonneg <;> linarith








end Basic



end Taper

end Zeta23
end

-- from Zeta23.Taper.Strip
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — Taper/Strip.lean.
[eq:hfbound] specialized to `f = φ`, `Λ_f = L/2` (as consumed by [prop:tail]):
"`|φ̂(r − iy)| ≤ e^{L/4} ‖φ''‖₁ |r − iy|⁻²`" for `|y| ≤ 1/2`.
All three statements are proved here from the general-`f` bounds in Zeta23/Poisson/PaperFT.lean,
and are consumed via `Zeta23.Params.norm_phiHat_*`.
Reference: the paper, §2.1 [eq:hfbound], §4 [prop:tail].
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform

namespace Zeta23

namespace Taper

section HfPhi
variable {ϱ : ℝ → ℝ} {L w : ℝ}


theorem phiC_support (hϱ : TaperProfile ϱ) (hw : 0 < w) :
    ∀ u, (phi ϱ L w u : ℂ) ≠ 0 → |u| ≤ L / 2 := by
  intro u hu
  by_contra h
  exact hu (by rw [phi_eq_zero hϱ hw (le_of_lt (not_le.mp h)), ofReal_zero])







end HfPhi

end Taper

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








/-! ### The paper's autocorrelation `(v ⋆ v)(y) := ∫ v(u) v(u+y) du` [eq:PhigA] versus Mathlib's convolution -/






/-! ## Fourier inversion in the paper's convention, cosine form -/


end Generic

/-! ## "`φ̂` and `Φ` are real, even, entire; …" (facts stated after [eq:PhigA]) -/

section PhigA
variable {ϱ : ℝ → ℝ} {L w : ℝ}

/-! #### auxiliary packaging of φ and φ² as inputs to the generic lemmas -/






/-- alias of `Strip.phiC_support`. -/
theorem phiC_supp (hϱ : TaperProfile ϱ) (hw : 0 < w) :
    ∀ u, (phi ϱ L w u : ℂ) ≠ 0 → |u| ≤ L / 2 := phiC_support hϱ hw





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
variable {ϱ : ℝ → ℝ} {L w : ℝ}

theorem solution (hϱ : TaperProfile ϱ) (hw : 0 < w) :
    ∀ u, (((phi ϱ L w u) ^ 2 : ℝ) : ℂ) ≠ 0 → |u| ≤ L / 2 := by
  intro u hu
  apply phiC_supp hϱ hw u
  intro h
  apply hu
  rw [Complex.ofReal_eq_zero] at h
  simp [h]
