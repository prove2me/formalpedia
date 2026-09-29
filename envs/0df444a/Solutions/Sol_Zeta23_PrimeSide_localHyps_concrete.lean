-- Prove2me | solution 1 for Zeta23.PrimeSide.localHyps_concrete
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T01:11:14.801895+00:00
-- url     : https://prove2.me/submissions/a89988d0-8bd4-491d-8205-277b7539a73a

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Mertens
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_Poisson
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs
import Definitions.Def_Zeta23_PrimeSideB_Concrete
import Definitions.Def_Zeta23_PrimeSideTemp
import Definitions.Def_Zeta23_Taper_Basic
import Definitions.Def_Zeta23_Taper_Params
import Theorems.Thm_Zeta23_PiX_abs_le
import Theorems.Thm_Zeta23_PiX_continuous
import Theorems.Thm_Zeta23_Taper_aConst_le_one
import Theorems.Thm_Zeta23_Taper_abs_PhiR_le_L
import Theorems.Thm_Zeta23_Taper_abs_PhiR_mul_abs_le
import Theorems.Thm_Zeta23_Taper_abs_PhiR_mul_sq_le
import Theorems.Thm_Zeta23_Taper_abs_le_psi_of_bounds
import Theorems.Thm_Zeta23_Taper_abs_phiHatR_mul_abs_le
import Theorems.Thm_Zeta23_Taper_abs_phiHatR_mul_sq_le
import Theorems.Thm_Zeta23_Taper_autocorr_le_of_support
import Theorems.Thm_Zeta23_Taper_bConst_le_aConst
import Theorems.Thm_Zeta23_Taper_contDiff_paperFT_ofReal
import Theorems.Thm_Zeta23_Taper_continuous_paperFT_ofReal
import Theorems.Thm_Zeta23_Taper_four_le_cRho
import Theorems.Thm_Zeta23_Taper_g_le_Aphi
import Theorems.Thm_Zeta23_Taper_hasSum_phiHatR_mul
import Theorems.Thm_Zeta23_Taper_integrable_phi_sq_mul_shift
import Theorems.Thm_Zeta23_Taper_integrable_re_paperFT_sq_and
import Theorems.Thm_Zeta23_Taper_integral_PhiR_sq_mul_cos
import Theorems.Thm_Zeta23_Taper_integral_PhiR_sq_mul_sq_le
import Theorems.Thm_Zeta23_Taper_integral_phiHatR_sq
import Theorems.Thm_Zeta23_Taper_integral_phiHatR_sq_mul_cos
import Theorems.Thm_Zeta23_Taper_integral_phiHatR_sq_mul_sq_le
import Theorems.Thm_Zeta23_Taper_integral_psi_Ioi_le
import Theorems.Thm_Zeta23_Taper_integral_psi_sq_le
import Theorems.Thm_Zeta23_Taper_integral_psi_sq_mul_abs_le
import Theorems.Thm_Zeta23_Taper_le_autocorr_of_plateau
import Theorems.Thm_Zeta23_Taper_norm_phiHat_le
import Theorems.Thm_Zeta23_Taper_one_sub_le_bConst
import Theorems.Thm_Zeta23_Taper_paperFT_neg_of_even
import Theorems.Thm_Zeta23_Taper_phiSqC_supp
import Theorems.Thm_Zeta23_Taper_phi_contDiff
import Theorems.Thm_Zeta23_Taper_phi_support_subset
import Theorems.Thm_Zeta23_Taper_psi_measurable
import Theorems.Thm_Zeta23_Taper_psi_mul_sq_le
import Theorems.Thm_Zeta23_Taper_psi_nonneg
import Theorems.Thm_Zeta23_Taper_psi_sq_integrable
import Theorems.Thm_Zeta23_Taper_psi_sq_mul_abs_integrable

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

theorem TaperProfile.nonneg {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ) (x : ℝ) : 0 ≤ ϱ x := by
  rw [← hϱ.eq_zero 0 le_rfl]
  rcases le_total 0 x with h | h
  · exact hϱ.monotone h
  · rw [hϱ.eq_zero x h, hϱ.eq_zero 0 le_rfl]

theorem TaperProfile.le_one {ϱ : ℝ → ℝ} (hϱ : TaperProfile ϱ) (x : ℝ) : ϱ x ≤ 1 := by
  rw [← hϱ.eq_one 1 le_rfl]
  rcases le_total x 1 with h | h
  · exact hϱ.monotone h
  · rw [hϱ.eq_one x h, hϱ.eq_one 1 le_rfl]


namespace Taper

/-! ### Constants depending only on ϱ  [eq:phinorms] -/






/-! ### The taper φ [eq:phidef], a, b [eq:abdef], Φ, g, A_φ [eq:PhigA], ψ [eq:psidef] -/

variable (ϱ : ℝ → ℝ) (L w : ℝ)











/-! ### Basic properties of φ (the sentence after [eq:phidef]):
"`φ ∈ C_c³(ℝ)` is even, `0 ≤ φ ≤ 1`, `supp φ = [−L/2, L/2]`, `φ = 1` on `[−L/2+w, L/2−w]`" -/

section Basic
variable {ϱ L w}

theorem phi_even (u : ℝ) : phi ϱ L w (-u) = phi ϱ L w u := by
  simp [phi, abs_neg]

theorem phi_nonneg (hϱ : TaperProfile ϱ) (u : ℝ) : 0 ≤ phi ϱ L w u := hϱ.nonneg _

theorem phi_le_one (hϱ : TaperProfile ϱ) (u : ℝ) : phi ϱ L w u ≤ 1 := hϱ.le_one _

/-- `φ(u) = 0` for `|u| ≥ L/2`. -/
theorem phi_eq_zero (hϱ : TaperProfile ϱ) (hw : 0 < w) {u : ℝ} (hu : L / 2 ≤ |u|) :
    phi ϱ L w u = 0 := by
  unfold phi
  apply hϱ.eq_zero
  apply div_nonpos_of_nonpos_of_nonneg <;> linarith

/-- `φ = 1` on `[−L/2 + w, L/2 − w]`. -/
theorem phi_eq_one (hϱ : TaperProfile ϱ) (hw : 0 < w) {u : ℝ} (hu : |u| ≤ L / 2 - w) :
    phi ϱ L w u = 1 := by
  unfold phi
  apply hϱ.eq_one
  rw [ge_iff_le, le_div_iff₀ hw]
  linarith


theorem phi_hasCompactSupport (hϱ : TaperProfile ϱ) (hw : 0 < w) :
    HasCompactSupport (phi ϱ L w) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (phi_support_subset hϱ hw)



theorem phi_continuous (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Continuous (phi ϱ L w) :=
  (phi_contDiff hϱ hw hwL).continuous

theorem phi_integrable (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Integrable (phi ϱ L w) :=
  (phi_continuous hϱ hw hwL).integrable_of_hasCompactSupport (phi_hasCompactSupport hϱ hw)

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

/-- `u ↦ (φ u : ℂ)` is `C³`. -/
theorem phiC_contDiff (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ContDiff ℝ 3 (fun u => (phi ϱ L w u : ℂ)) :=
  ofRealCLM.contDiff.comp (phi_contDiff hϱ hw hwL)

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
section
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



/-! ### The paper's autocorrelation `(v ⋆ v)(y) := ∫ v(u) v(u+y) du` [eq:PhigA] versus Mathlib's convolution -/






/-! ## Fourier inversion in the paper's convention, cosine form -/


end Generic

/-! ## "`φ̂` and `Φ` are real, even, entire; …" (facts stated after [eq:PhigA]) -/

section PhigA
variable {ϱ : ℝ → ℝ} {L w : ℝ}

/-! #### auxiliary packaging of φ and φ² as inputs to the generic lemmas -/

theorem phi_sq_even (u : ℝ) : phi ϱ L w (-u) ^ 2 = phi ϱ L w u ^ 2 := by rw [phi_even]


theorem phiC_continuous (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Continuous (fun u => (phi ϱ L w u : ℂ)) :=
  Complex.continuous_ofReal.comp (phi_continuous hϱ hw hwL)

theorem phiC_hasCompactSupport (hϱ : TaperProfile ϱ) (hw : 0 < w) :
    HasCompactSupport (fun u => (phi ϱ L w u : ℂ)) :=
  (phi_hasCompactSupport hϱ hw).comp_left Complex.ofReal_zero

theorem phiC_contDiff_two (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ContDiff ℝ 2 (fun u => (phi ϱ L w u : ℂ)) :=
  (phiC_contDiff hϱ hw hwL).of_le (by norm_num)

/-- alias of `Strip.phiC_support`. -/
theorem phiC_supp (hϱ : TaperProfile ϱ) (hw : 0 < w) :
    ∀ u, (phi ϱ L w u : ℂ) ≠ 0 → |u| ≤ L / 2 := phiC_support hϱ hw

theorem phiSqC_continuous (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Continuous (fun u => (((phi ϱ L w u) ^ 2 : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp ((phi_continuous hϱ hw hwL).pow 2)

theorem phiSqC_hasCompactSupport (hϱ : TaperProfile ϱ) (hw : 0 < w) :
    HasCompactSupport (fun u => (((phi ϱ L w u) ^ 2 : ℝ) : ℂ)) :=
  (phi_hasCompactSupport hϱ hw).comp_left (g := fun x : ℝ => ((x ^ 2 : ℝ) : ℂ)) (by simp)

theorem phiSqC_contDiff_two (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ContDiff ℝ 2 (fun u => (((phi ϱ L w u) ^ 2 : ℝ) : ℂ)) := by
  have := Complex.ofRealCLM.contDiff.comp (((phi_contDiff hϱ hw hwL).pow 2).of_le (m := 2) (by norm_num))
  simpa [Function.comp_def] using this


/-! #### real / even / conjugation symmetry (hypothesis-free: only "φ real and even" is used) -/




theorem phiHatR_even (r : ℝ) : phiHatR ϱ L w (-r) = phiHatR ϱ L w r := by
  simp only [phiHatR, phiHat, Complex.ofReal_neg, paperFT_neg_of_even phi_even]

theorem PhiR_even (r : ℝ) : PhiR ϱ L w (-r) = PhiR ϱ L w r := by
  simp only [PhiR, Phi, Complex.ofReal_neg]
  rw [paperFT_neg_of_even (v := fun u => phi ϱ L w u ^ 2) phi_sq_even]

/-! #### continuity / differentiability on ℝ ("entire" is more than any consumer needs) -/

theorem phiHatR_continuous (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Continuous (phiHatR ϱ L w) :=
  (contDiff_re_paperFT_ofReal (phiC_continuous hϱ hw hwL) (phiC_hasCompactSupport hϱ hw)
    0).continuous


/-- `Φ` is `C¹` on ℝ (indeed entire; C¹ is what [prop:cross] differentiates). -/
theorem PhiR_contDiff_one (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ContDiff ℝ 1 (PhiR ϱ L w) :=
  contDiff_re_paperFT_ofReal (phiSqC_continuous hϱ hw hwL) (phiSqC_hasCompactSupport hϱ hw) 1

/-! #### values at 0 -/

/-- `h_f(0) = ∫ f` for a real `f` (cast to ℂ). -/
theorem paperFT_ofReal_zero (f : ℝ → ℝ) :
    paperFT (fun u => (f u : ℂ)) 0 = ((∫ u, f u : ℝ) : ℂ) := by
  simp only [paperFT, mul_zero, zero_mul, Complex.exp_zero, mul_one]
  exact integral_complex_ofReal


/-- "`Φ(0) = aL`". -/
theorem PhiR_zero (_hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    PhiR ϱ L w 0 = aConst ϱ L w * L := by
  have hL : L ≠ 0 := by linarith
  rw [PhiR, Phi, Complex.ofReal_zero, paperFT_ofReal_zero, Complex.ofReal_re, aConst,
    mul_comm, ← mul_assoc, mul_inv_cancel₀ hL, one_mul]

theorem g_zero (_hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    g ϱ L w 0 = bConst ϱ L w * L := by
  have hL : L ≠ 0 := by linarith
  rw [g, Params.autocorr, bConst, mul_comm, ← mul_assoc, mul_inv_cancel₀ hL, one_mul]
  congr 1; funext u; rw [add_zero]; ring


/-! #### "`φ̂² = Â_φ` and `Φ² = ĝ` on ℝ" — convolution theorem -/



/-! #### integrability of `φ̂², φ̂²|r|, Φ², Φ²|r|` (decay [eq:hfbound] via PaperFT.lean) -/

theorem integrable_phiHatR_sq (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Integrable (fun r => phiHatR ϱ L w r ^ 2) :=
  (integrable_re_paperFT_sq_and (phiC_contDiff_two hϱ hw hwL) (phiC_supp hϱ hw)).1

theorem integrable_phiHatR_sq_mul_abs (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Integrable (fun r => phiHatR ϱ L w r ^ 2 * |r|) :=
  (integrable_re_paperFT_sq_and (phiC_contDiff_two hϱ hw hwL) (phiC_supp hϱ hw)).2

theorem integrable_PhiR_sq (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Integrable (fun x => PhiR ϱ L w x ^ 2) :=
  (integrable_re_paperFT_sq_and (phiSqC_contDiff_two hϱ hw hwL) (phiSqC_supp hϱ hw)).1

theorem integrable_PhiR_sq_mul_abs (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Integrable (fun x => PhiR ϱ L w x ^ 2 * |x|) :=
  (integrable_re_paperFT_sq_and (phiSqC_contDiff_two hϱ hw hwL) (phiSqC_supp hϱ hw)).2

/-! #### Plancherel / inversion identities -/




/-- "`∫_ℝ Φ² = 2π g(0) = 2π b L`". -/
theorem integral_PhiR_sq (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ∫ r, PhiR ϱ L w r ^ 2 = 2 * π * bConst ϱ L w * L := by
  have h := integral_PhiR_sq_mul_cos hϱ hw hwL 0
  simp only [mul_zero, Real.cos_zero, mul_one] at h
  rw [h, g_zero hϱ hw hwL]
  ring

end PhigA

end Taper

end Zeta23
end

-- from Zeta23.Poisson
section
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

theorem w_pos' (hP : P.Valid) : 0 < P.w := lt_of_lt_of_le one_pos hP.one_le_w

variable (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
include hP hwL

/-- [lem:poisson] for the paper's data: for all real τ, τ',
`HasSum (k ↦ φ̂(τ − τ_k) φ̂(τ' − τ_k)) (L Φ(τ − τ'))`, `τ_k = P.tau T k = T + k·(2π/L)`. -/
theorem hasSum_phiHatR_mul (τ τ' : ℝ) :
    HasSum (fun k : ℤ => P.phiHatR T (τ - P.tau T k) * P.phiHatR T (τ' - P.tau T k))
      (P.L T * P.PhiR T (τ - τ')) :=
  Taper.hasSum_phiHatR_mul hP.taper (w_pos' hP) (by linarith [hP.one_le_w]) T τ τ'



end Params

end Zeta23
end

-- from Zeta23.PrimeSideB.Concrete
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
  Part of the Zeta23 formalization of the paper
  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/

/-!
# The concrete prime-side data as an instance of the abstract layer
Small, dependency-light file (imports only `PrimeSideA.Basic` and `PrimeSideTemp`):

* `Params.toSetting P T = ⟨T, λ, w⟩`, `Params.localFun P T = ⟨φ̂|_ℝ, Φ|_ℝ, A_φ, g, a, b⟩(T)` and the
  `rfl` bridges (`trGtA (P.toSetting T) (P.localFun T) = P.trGtilde T`, …);
* `PrimeSide.LocalHypsEventually cϱ P` — "the taper facts `LocalHyps` hold for the concrete data for
  all large `T`" (proved in `Zeta23/PrimeSideA/Bridge.lean`);
* `PrimeSide.evBound_of_eventuallyAt` — an `EventuallyAt`-form result specialised to the concrete
  data is an `EvBound` in `T`.
-/

noncomputable section

open Real Filter Topology MeasureTheory
open scoped BigOperators ArithmeticFunction

namespace Zeta23

namespace Params
variable (P : Params) (T : ℝ)



@[simp] lemma toSetting_T : (P.toSetting T).T = T := rfl
@[simp] lemma toSetting_lam : (P.toSetting T).lam = P.lam := rfl
@[simp] lemma toSetting_w : (P.toSetting T).w = P.w := rfl
@[simp] lemma toSetting_L : (P.toSetting T).L = P.L T := rfl
@[simp] lemma toSetting_X : (P.toSetting T).X = P.X T := rfl
@[simp] lemma toSetting_l : (P.toSetting T).l = l T := rfl
@[simp] lemma toSetting_ell1 : (P.toSetting T).ell1 = ell1 T := rfl
@[simp] lemma toSetting_d : (P.toSetting T).d = P.d T := rfl
@[simp] lemma toSetting_tau (k : ℤ) : (P.toSetting T).tau k = P.tau T k := rfl
@[simp] lemma localFun_a : (P.localFun T).a = P.a T := rfl
@[simp] lemma localFun_b : (P.localFun T).b = P.b T := rfl
@[simp] lemma localFun_Phi : (P.localFun T).Phi = P.PhiR T := rfl
@[simp] lemma localFun_g : (P.localFun T).g = P.g T := rfl
@[simp] lemma localFun_phiHat : (P.localFun T).phiHat = P.phiHatR T := rfl

end Params

namespace PrimeSide

variable (P : Params) (T : ℝ)





variable {P}




end PrimeSide

end Zeta23

end
end

-- from Zeta23.Taper.Decay
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — Taper/Decay.lean.  Two sections, `GBounds` and `Psi`.
Names and statements here are used by the umbrella Zeta23/Taper.lean (and the Params layer)
and by downstream files.
Canonical text: the paper, §2.2 [subsec:family].  See Zeta23/Taper.lean header for conventions:
generic parameters (ϱ : ℝ → ℝ) (L w : ℝ); paper's side condition is 1 ≤ w ≤ L/8 [eq:wrange];
each lemma carries the minimal hypothesis it needs.
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform

namespace Zeta23

namespace Taper

/-! ### [eq:gbounds]: "`(L − 2w − |y|)₊ ≤ g(y) ≤ A_φ(y) ≤ (L − |y|)₊`" -/

section GBounds

variable {ϱ : ℝ → ℝ} {L w : ℝ}

/-! Helpers on the autocorrelation `(v ⋆ v)(y) := ∫ v(u) v(u+y) du` [eq:PhigA] of a real function:
evenness (translation invariance of Lebesgue measure), the interval-overlap length
`|[−M,M] ∩ ([−M,M] − y)| = (2M − |y|)₊`, the two comparison bounds, vanishing for `|y| ≥ 2M`,
and continuity in `y` (parametric integral over the compact support). -/








/-! The taper instances: `A_φ = φ ⋆ φ` (support `[−L/2, L/2]`, `0 ≤ φ ≤ 1`) and `g = φ² ⋆ φ²`
(plateau `φ² = 1` on `[−L/2+w, L/2−w]`). -/






theorem g_ge (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (y : ℝ) :
    max (L - 2 * w - |y|) 0 ≤ g ϱ L w y := by
  have h := le_autocorr_of_plateau (fun u => phi ϱ L w u ^ 2) (M := L / 2 - w)
    (fun u => sq_nonneg _)
    (fun u hu => by show phi ϱ L w u ^ 2 = 1; rw [phi_eq_one hϱ hw hu, one_pow])
    (integrable_phi_sq_mul_shift hϱ hw hwL y)
  rw [show 2 * (L / 2 - w) = L - 2 * w by ring] at h
  exact h


theorem Aphi_le (hϱ : TaperProfile ϱ) (hw : 0 < w) (_hwL : 2 * w ≤ L) (y : ℝ) :
    Aphi ϱ L w y ≤ max (L - |y|) 0 := by
  have h := autocorr_le_of_support (phi ϱ L w) (M := L / 2) (phi_nonneg hϱ) (phi_le_one hϱ)
    (fun u hu => phi_eq_zero hϱ hw hu) y
  rw [show 2 * (L / 2) = L by ring] at h
  exact h







end GBounds

/-! ### [eq:psidef]: "`max(|φ̂(r)|, |Φ(r)|) ≤ ψ(r) := min(L, 2/|r|, c_ϱ/(w r²))`"
We give the three bounds separately (division-free) and then the `ψ` form. -/

section Psi 
variable {ϱ : ℝ → ℝ} {L w : ℝ}

/-! #### Helpers: first-order [eq:hfbound], and the ℂ-valued φ² -/


/-- The ℂ-valued φ² used in Φ := (φ²)^ is C² with support in [−L/2, L/2]. -/
theorem phiSqC_contDiff (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ContDiff ℝ 2 (fun u => (((phi ϱ L w u) ^ 2 : ℝ) : ℂ)) := by
  have h : ContDiff ℝ 2 (fun u => (phi ϱ L w u) ^ 2) :=
    ((phi_contDiff hϱ hw hwL).of_le (by norm_num)).pow 2
  exact ofRealCLM.contDiff.comp h

theorem phiSqC_support (hϱ : TaperProfile ϱ) (hw : 0 < w) (u : ℝ)
    (hu : (((phi ϱ L w u) ^ 2 : ℝ) : ℂ) ≠ 0) : |u| ≤ L / 2 := by
  by_contra h
  apply hu
  rw [phi_eq_zero hϱ hw (le_of_lt (not_le.mp h))]
  simp




theorem abs_phiHatR_le_norm (r : ℝ) : |phiHatR ϱ L w r| ≤ ‖phiHat ϱ L w r‖ :=
  Complex.abs_re_le_norm _


theorem abs_phiHatR_le_L (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (r : ℝ) :
    |phiHatR ϱ L w r| ≤ L := by
  refine (abs_phiHatR_le_norm r).trans ?_
  have h := norm_phiHat_le hϱ hw hwL (r : ℂ)
  simpa using h







theorem abs_phiHatR_le_psi (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 2 * w ≤ L) (r : ℝ) :
    |phiHatR ϱ L w r| ≤ psi ϱ L w r :=
  abs_le_psi_of_bounds (by linarith) (abs_phiHatR_le_L hϱ (by linarith) hwL)
    (abs_phiHatR_mul_abs_le hϱ (by linarith) hwL) (abs_phiHatR_mul_sq_le hϱ hw hwL) r

theorem abs_PhiR_le_psi (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 2 * w ≤ L) (r : ℝ) :
    |PhiR ϱ L w r| ≤ psi ϱ L w r :=
  abs_le_psi_of_bounds (by linarith) (abs_PhiR_le_L hϱ (by linarith) hwL)
    (abs_PhiR_mul_abs_le hϱ (by linarith) hwL) (abs_PhiR_mul_sq_le hϱ hw hwL) r



theorem psi_le_L (_hϱ : TaperProfile ϱ) (_hw : 1 ≤ w) (_hwL : 2 * w ≤ L) (r : ℝ) :
    psi ϱ L w r ≤ L := by
  unfold psi
  split_ifs with hr
  · exact le_rfl
  · exact min_le_left _ _



/-! #### Measurability / integrability of ψ -/

theorem psi_abs (r : ℝ) : psi ϱ L w |r| = psi ϱ L w r := by
  unfold psi
  simp only [abs_eq_zero, abs_abs, sq_abs]


/-- For r > 0: ψ(r) ≤ (c_ϱ/w) · r^{−2} (rpow form). -/
theorem psi_le_rpow_neg_two (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 2 * w ≤ L) {r : ℝ}
    (hr : 0 < r) : psi ϱ L w r ≤ cRho ϱ / w * r ^ (-2:ℝ) := by
  have h := psi_mul_sq_le hϱ hw hwL r
  rw [Real.rpow_neg hr.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast,
    ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  exact h

/-- The common integrable plateau majorant: `a` on [−1,1] and `b·|r|⁻²` outside (ψ: a = L, b = c_ϱ/w;
r²-moments: a = 4, b = C²).  ∫ = 2a + 2b. -/
noncomputable def plateauMaj (a b : ℝ) (r : ℝ) : ℝ :=
  (Icc (-1:ℝ) 1).indicator (fun _ => a) r
    + b * ((Ioi (1:ℝ)).indicator (fun x => x ^ (-2:ℝ)) r + (Ioi (1:ℝ)).indicator (fun x => x ^ (-2:ℝ)) (-r))

theorem tail_indicator_integrable :
    Integrable ((Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ))) :=
  (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).integrable_indicator measurableSet_Ioi

theorem plateauMaj_integrable (a b : ℝ) : Integrable (plateauMaj a b) :=
  ((integrable_indicator_iff measurableSet_Icc).mpr (integrableOn_const (by simp))).add
    ((tail_indicator_integrable.add tail_indicator_integrable.comp_neg).const_mul _)


/-- The integrable majorant of ψ: L on [−1,1] and (c_ϱ/w)|r|⁻² outside. -/
noncomputable abbrev psiMaj (ϱ : ℝ → ℝ) (L w : ℝ) : ℝ → ℝ := plateauMaj L (cRho ϱ / w)

theorem psiMaj_integrable : Integrable (psiMaj ϱ L w) := plateauMaj_integrable _ _

theorem psi_le_psiMaj (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 2 * w ≤ L) (r : ℝ) :
    psi ϱ L w r ≤ psiMaj ϱ L w r := by
  have hw0 : 0 < w := by linarith
  have hc : 0 ≤ cRho ϱ := le_trans (by norm_num) (four_le_cRho hϱ)
  have hind : ∀ s : ℝ, 0 ≤ (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) s := fun s =>
    Set.indicator_nonneg (fun x hx => Real.rpow_nonneg (le_trans zero_le_one (le_of_lt hx)) _) _
  unfold psiMaj plateauMaj
  by_cases h : r ∈ Icc (-1:ℝ) 1
  · rw [Set.indicator_of_mem h]
    have := psi_le_L hϱ hw hwL r
    nlinarith [hind r, hind (-r), div_nonneg hc hw0.le]
  · rw [Set.indicator_of_notMem h, zero_add]
    rw [mem_Icc, not_and_or, not_le, not_le] at h
    rcases h with h | h
    · -- r < -1
      have hr : 0 < -r := by linarith
      rw [Set.indicator_of_notMem (show r ∉ Ioi (1:ℝ) by simp; linarith),
        Set.indicator_of_mem (show -r ∈ Ioi (1:ℝ) by simp; linarith), zero_add]
      have := psi_le_rpow_neg_two hϱ hw hwL hr
      rw [← psi_abs, abs_of_neg (by linarith)]
      exact this
    · -- 1 < r
      have hr : 0 < r := by linarith
      rw [Set.indicator_of_mem (show r ∈ Ioi (1:ℝ) from h),
        Set.indicator_of_notMem (show -r ∉ Ioi (1:ℝ) by simp; linarith), add_zero]
      exact psi_le_rpow_neg_two hϱ hw hwL hr


theorem continuous_phiHatR_aux (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Continuous (phiHatR ϱ L w) := by
  unfold phiHatR phiHat
  exact Complex.continuous_re.comp
    (continuous_paperFT_ofReal (phi_integrable hϱ hw hwL).ofReal)

theorem continuous_PhiR_aux (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    Continuous (PhiR ϱ L w) := by
  unfold PhiR Phi
  refine Complex.continuous_re.comp (continuous_paperFT_ofReal ?_)
  exact (phiSqC_contDiff hϱ hw hwL).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_of_support_subset_abs (phiSqC_support hϱ hw))

/-! ### [eq:psiints].  We record upper bounds — every downstream citation of [eq:psiints] in §5 is
"≪ log L" or "≤ 8L".  (Paper: "a direct computation (split at |r| = 2/L and |r| = c_ϱ/2w; note
c_ϱ L/4w ≥ 1 by [eq:wrange]) gives Ψ₀ = 4 + 2 log(c_ϱ L/4w), ∫ψ²|r| = 8 + 8 log(c_ϱ L/4w),
∫ψ² ≤ 8L".) -/






theorem psi_integrable (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    Integrable (psi ϱ L w) := by
  have hwL' : 2 * w ≤ L := by linarith
  refine (psiMaj_integrable (ϱ := ϱ) (L := L) (w := w)).mono'
    psi_measurable.aestronglyMeasurable (Eventually.of_forall fun r => ?_)
  rw [Real.norm_of_nonneg (psi_nonneg hϱ hw hwL' r)]
  exact psi_le_psiMaj hϱ hw hwL' r



/-! #### Generic moment bounds from |F| ≤ ψ-type information -/

/-- If |F| ≤ ψ pointwise then ∫ F²|r| ≤ ∫ ψ²|r| ≤ 8 + 8 log(c_ϱ L/4w). -/
theorem integral_sq_mul_abs_le_of_le_psi (hϱ : TaperProfile ϱ) (hw : 1 ≤ w)
    (hwL : 8 * w ≤ L) {F : ℝ → ℝ} (hF : ∀ r, |F r| ≤ psi ϱ L w r) :
    ∫ r, F r ^ 2 * |r| ≤ 8 + 8 * Real.log (cRho ϱ * L / (4 * w)) := by
  refine le_trans (integral_mono_of_nonneg (Eventually.of_forall fun r => by positivity)
    (psi_sq_mul_abs_integrable hϱ hw hwL) (Eventually.of_forall fun r => ?_))
    (integral_psi_sq_mul_abs_le hϱ hw hwL)
  have h : F r ^ 2 ≤ psi ϱ L w r ^ 2 := by
    rw [← sq_abs (F r)]
    exact pow_le_pow_left₀ (abs_nonneg _) (hF r) 2
  exact mul_le_mul_of_nonneg_right h (abs_nonneg r)

/-- The integrable majorant for the r²-moments: 4 on [−1,1] and C²|r|⁻² outside. -/
noncomputable abbrev momMaj (C : ℝ) : ℝ → ℝ := plateauMaj 4 (C ^ 2)

theorem momMaj_integrable (C : ℝ) : Integrable (momMaj C) := plateauMaj_integrable _ _


/-- Pointwise: |F(r)|·|r| ≤ 2 and |F(r)|·r² ≤ C give F(r)² r² ≤ momMaj C r. -/
theorem sq_mul_sq_le_momMaj {F : ℝ → ℝ} {C : ℝ} (_hC : 0 ≤ C)
    (h1 : ∀ r, |F r| * |r| ≤ 2) (h2 : ∀ r, |F r| * r ^ 2 ≤ C) (r : ℝ) :
    F r ^ 2 * r ^ 2 ≤ momMaj C r := by
  have hind : ∀ s : ℝ, 0 ≤ (Ioi (1:ℝ)).indicator (fun x : ℝ => x ^ (-2:ℝ)) s := fun s =>
    Set.indicator_nonneg (fun x hx => Real.rpow_nonneg (le_trans zero_le_one (le_of_lt hx)) _) _
  have hsq : ∀ s : ℝ, 1 < s → F r ^ 2 * s ^ 2 * s ^ 2 ≤ C ^ 2 → F r ^ 2 * s ^ 2 ≤ C ^ 2 * s ^ (-2:ℝ) := by
    intro s hs h
    have hs0 : 0 < s := by linarith
    rw [Real.rpow_neg hs0.le, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast,
      ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    exact h
  unfold momMaj plateauMaj
  by_cases h : r ∈ Icc (-1:ℝ) 1
  · rw [Set.indicator_of_mem h]
    have hb : F r ^ 2 * r ^ 2 ≤ 4 := by
      have := h1 r
      have h0 : 0 ≤ |F r| * |r| := by positivity
      calc F r ^ 2 * r ^ 2 = (|F r| * |r|) ^ 2 := by rw [mul_pow, sq_abs, sq_abs]
        _ ≤ 2 ^ 2 := pow_le_pow_left₀ h0 this 2
        _ = 4 := by norm_num
    nlinarith [hind r, hind (-r), sq_nonneg C]
  · rw [Set.indicator_of_notMem h, zero_add]
    rw [mem_Icc, not_and_or, not_le, not_le] at h
    have hFsq : F r ^ 2 * r ^ 2 * r ^ 2 ≤ C ^ 2 := by
      have := h2 r
      have h0 : 0 ≤ |F r| * r ^ 2 := by positivity
      calc F r ^ 2 * r ^ 2 * r ^ 2 = (|F r| * r ^ 2) ^ 2 := by rw [mul_pow, sq_abs]; ring
        _ ≤ C ^ 2 := pow_le_pow_left₀ h0 this 2
    rcases h with h | h
    · -- r < -1
      rw [Set.indicator_of_notMem (show r ∉ Ioi (1:ℝ) by simp; linarith),
        Set.indicator_of_mem (show -r ∈ Ioi (1:ℝ) by simp; linarith), zero_add]
      have := hsq (-r) (by linarith) (by simpa using hFsq)
      simpa using this
    · -- 1 < r
      rw [Set.indicator_of_mem (show r ∈ Ioi (1:ℝ) from h),
        Set.indicator_of_notMem (show -r ∉ Ioi (1:ℝ) by simp; linarith), add_zero]
      exact hsq r h hFsq

theorem integrable_sq_mul_sq_of_bounds {F : ℝ → ℝ} {C : ℝ} (hFc : Continuous F)
    (hC : 0 ≤ C) (h1 : ∀ r, |F r| * |r| ≤ 2) (h2 : ∀ r, |F r| * r ^ 2 ≤ C) :
    Integrable (fun r => F r ^ 2 * r ^ 2) := by
  refine (momMaj_integrable C).mono' (by fun_prop) (Eventually.of_forall fun r => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  exact sq_mul_sq_le_momMaj hC h1 h2 r


/-- Consequence packaged for [prop:trace]/[prop:mumu]: ∫ φ̂(r)² |r| dr ≤ 8 + 8 log(c_ϱ L/4w). -/
theorem integral_phiHatR_sq_mul_abs_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    ∫ r, phiHatR ϱ L w r ^ 2 * |r| ≤ 8 + 8 * Real.log (cRho ϱ * L / (4 * w)) :=
  integral_sq_mul_abs_le_of_le_psi hϱ hw hwL
    (fun r => abs_phiHatR_le_psi hϱ hw (by linarith) r)

theorem integral_PhiR_sq_mul_abs_le (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    ∫ x, PhiR ϱ L w x ^ 2 * |x| ≤ 8 + 8 * Real.log (cRho ϱ * L / (4 * w)) :=
  integral_sq_mul_abs_le_of_le_psi hϱ hw hwL
    (fun r => abs_PhiR_le_psi hϱ hw (by linarith) r)

/-- Used for [prop:trace] (μ/Π tails): `φ̂(r)² r²` is integrable … -/
theorem integrable_phiHatR_sq_mul_sq (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    Integrable (fun r => phiHatR ϱ L w r ^ 2 * r ^ 2) := by
  have hw0 : 0 < w := by linarith
  have hwL' : 2 * w ≤ L := by linarith
  exact integrable_sq_mul_sq_of_bounds (continuous_phiHatR_aux hϱ hw0 hwL')
    (div_nonneg (le_trans (by norm_num) (four_le_cRho hϱ)) hw0.le)
    (abs_phiHatR_mul_abs_le hϱ hw0 hwL') (abs_phiHatR_mul_sq_le hϱ hw hwL')


/-- Φ analogue (used for [prop:mumu]): `Φ(x)² x²` integrable … -/
theorem integrable_PhiR_sq_mul_sq (hϱ : TaperProfile ϱ) (hw : 1 ≤ w) (hwL : 8 * w ≤ L) :
    Integrable (fun x => PhiR ϱ L w x ^ 2 * x ^ 2) := by
  have hw0 : 0 < w := by linarith
  have hwL' : 2 * w ≤ L := by linarith
  exact integrable_sq_mul_sq_of_bounds (continuous_PhiR_aux hϱ hw0 hwL')
    (div_nonneg (le_trans (by norm_num) (four_le_cRho hϱ)) hw0.le)
    (abs_PhiR_mul_abs_le hϱ hw0 hwL') (abs_PhiR_mul_sq_le hϱ hw hwL')


end Psi


end Taper

end Zeta23
end

-- from Zeta23.Taper.Params
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — Taper/Params.lean.  Consumer-facing layer, part 1:
the `P : Params`, `T : ℝ` versions of everything that depends only on Taper/Basic, Taper/Norms
and Taper/Strip (φ facts [eq:phidef], [eq:abdef], C₁ and [eq:hfbound] for φ), plus the rfl
bridges to Defs.  Split out of Zeta23/Taper.lean so that Zeta23/Main.lean can import it without
pulling Taper/Decay, Taper/Fourier.  Hypotheses: `hP : P.Valid`,
`hwL : 8 * P.w ≤ P.L T` ([eq:wrange]).  The remaining Params-layer facts (φ̂/Φ, ψ, g, A_φ,
Plancherel) are in the umbrella Zeta23/Taper.lean.
-/

open Complex MeasureTheory Real Set Filter Topology

namespace Zeta23

namespace Params

variable (P : Params) (T : ℝ)

theorem crho_eq : P.crho = Taper.cRho P.ϱ := rfl




variable {P T}

theorem w_pos (hP : P.Valid) : 0 < P.w := lt_of_lt_of_le one_pos hP.one_le_w
theorem two_w_le (hwL : 8 * P.w ≤ P.L T) (hP : P.Valid) : 2 * P.w ≤ P.L T := by
  linarith [hP.one_le_w]

/-! #### hypothesis-free facts -/

section
variable (hP : P.Valid)
include hP
end

section
variable (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
include hP hwL

/-! #### φ -/

/-! #### [eq:abdef] -/
theorem b_le_a : P.b T ≤ P.a T := Taper.bConst_le_aConst hP.taper (w_pos hP) (two_w_le hwL hP)
theorem a_le_one : P.a T ≤ 1 := Taper.aConst_le_one hP.taper (w_pos hP) (two_w_le hwL hP)
theorem one_sub_le_b : 1 - 2 * P.w / P.L T ≤ P.b T :=
  Taper.one_sub_le_bConst hP.taper (w_pos hP) (two_w_le hwL hP)

/-! #### [eq:hfbound] for φ ([prop:tail]) -/

end

end Params

end Zeta23
end

-- from Zeta23.Taper
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Taper.lean — the test family [subsec:family] of the paper §2.2 and its
elementary facts: text after [eq:phidef], [eq:phinorms], [eq:abdef], the facts after [eq:PhigA]
(incl. [eq:Phi2FT]), [eq:gbounds], [eq:psidef], [eq:psiints], and [eq:hfbound] specialized to φ.
([eq:hfbound] for general f is in `Zeta23.Poisson.PaperFT`.)

SUB-FILES: Zeta23/Taper/Basic.lean (defs + [eq:phidef] facts),
Norms.lean ([eq:phinorms], [eq:abdef]), Strip.lean ([eq:hfbound] for φ),
Decay.lean ([eq:gbounds], [eq:psidef], [eq:psiints]),
Fourier.lean ([eq:PhigA]-line facts, Plancherel, [eq:Phi2FT]).  This umbrella file
holds the consumer-facing `Params` layer, part 2 (φ̂/Φ/ψ/g/A_φ facts); part 1 (φ, a, b, C₁,
hfbound — depends only on Basic/Norms/Strip) is Zeta23/Taper/Params.lean, importable on its own.

ORGANIZATION.  Namespace `Zeta23.Taper`: generic parameters `(ϱ : ℝ → ℝ) (L w : ℝ)` — pure
one-variable calculus, no `T`.  Namespace `Zeta23.Params` (last section): the same facts for
`P : Params`, `T : ℝ` of Zeta23/Defs.lean (`L = P.L T`, `w = P.w`, `ϱ = P.ϱ`); the bridges
`P.phi T = Taper.phi P.ϱ (P.L T) P.w` etc. are `rfl`.  Consumers use the `Params` versions.

Side conditions: the paper fixes `1 ≤ w ≤ L/8` [eq:wrange].  Generic lemmas carry the minimal
hypothesis they need (`0 < w`, `2w ≤ L`, …); the `Params` versions uniformly assume
`hP : P.Valid` (gives `1 ≤ w`, `TaperProfile ϱ`) and `hwL : 8 * P.w ≤ P.L T` ([eq:wrange]).
-/

open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform

namespace Zeta23

/-! ## Instantiation for `P : Params`, `T : ℝ` (Zeta23/Defs.lean).
Consumer-facing names.  Hypotheses: `hP : P.Valid`, `hwL : 8 * P.w ≤ P.L T` ([eq:wrange]). -/

namespace Params

variable {P : Params} {T : ℝ}

/-! #### hypothesis-free facts -/
theorem phiHatR_even (r : ℝ) : P.phiHatR T (-r) = P.phiHatR T r := Taper.phiHatR_even r
theorem PhiR_even (r : ℝ) : P.PhiR T (-r) = P.PhiR T r := Taper.PhiR_even r

section
variable (hP : P.Valid) (hwL : 8 * P.w ≤ P.L T)
include hP hwL

/-! #### φ̂, Φ real/even/continuous; conj symmetry -/
theorem phiHatR_continuous : Continuous (P.phiHatR T) :=
  Taper.phiHatR_continuous hP.taper (w_pos hP) (two_w_le hwL hP)
theorem PhiR_contDiff_one : ContDiff ℝ 1 (P.PhiR T) :=
  Taper.PhiR_contDiff_one hP.taper (w_pos hP) (two_w_le hwL hP)

/-! #### [eq:PhigA]-line facts -/
theorem PhiR_zero : P.PhiR T 0 = P.a T * P.L T :=
  Taper.PhiR_zero hP.taper (w_pos hP) (two_w_le hwL hP)
theorem integral_phiHatR_sq : ∫ r, P.phiHatR T r ^ 2 = 2 * π * P.a T * P.L T :=
  Taper.integral_phiHatR_sq hP.taper (w_pos hP) (two_w_le hwL hP)
theorem integral_PhiR_sq : ∫ r, P.PhiR T r ^ 2 = 2 * π * P.b T * P.L T :=
  Taper.integral_PhiR_sq hP.taper (w_pos hP) (two_w_le hwL hP)
theorem integral_phiHatR_sq_mul_cos (y : ℝ) :
    ∫ r, P.phiHatR T r ^ 2 * Real.cos (r * y) = 2 * π * P.Aphi T y :=
  Taper.integral_phiHatR_sq_mul_cos hP.taper (w_pos hP) (two_w_le hwL hP) y
theorem integral_PhiR_sq_mul_cos (y : ℝ) :
    ∫ x, P.PhiR T x ^ 2 * Real.cos (x * y) = 2 * π * P.g T y :=
  Taper.integral_PhiR_sq_mul_cos hP.taper (w_pos hP) (two_w_le hwL hP) y
theorem integrable_phiHatR_sq : Integrable (fun r => P.phiHatR T r ^ 2) :=
  Taper.integrable_phiHatR_sq hP.taper (w_pos hP) (two_w_le hwL hP)
theorem integrable_phiHatR_sq_mul_abs : Integrable (fun r => P.phiHatR T r ^ 2 * |r|) :=
  Taper.integrable_phiHatR_sq_mul_abs hP.taper (w_pos hP) (two_w_le hwL hP)
theorem integrable_PhiR_sq : Integrable (fun x => P.PhiR T x ^ 2) :=
  Taper.integrable_PhiR_sq hP.taper (w_pos hP) (two_w_le hwL hP)
theorem integrable_PhiR_sq_mul_abs : Integrable (fun x => P.PhiR T x ^ 2 * |x|) :=
  Taper.integrable_PhiR_sq_mul_abs hP.taper (w_pos hP) (two_w_le hwL hP)
theorem integral_phiHatR_sq_mul_abs_le :
    ∫ r, P.phiHatR T r ^ 2 * |r| ≤ 8 + 8 * Real.log (P.crho * P.L T / (4 * P.w)) :=
  Taper.integral_phiHatR_sq_mul_abs_le hP.taper hP.one_le_w hwL
theorem integral_PhiR_sq_mul_abs_le :
    ∫ x, P.PhiR T x ^ 2 * |x| ≤ 8 + 8 * Real.log (P.crho * P.L T / (4 * P.w)) :=
  Taper.integral_PhiR_sq_mul_abs_le hP.taper hP.one_le_w hwL
theorem integrable_phiHatR_sq_mul_sq : Integrable (fun r => P.phiHatR T r ^ 2 * r ^ 2) :=
  Taper.integrable_phiHatR_sq_mul_sq hP.taper hP.one_le_w hwL
theorem integral_phiHatR_sq_mul_sq_le : ∫ r, P.phiHatR T r ^ 2 * r ^ 2 ≤ 8 + 2 * (P.crho / P.w) ^ 2 :=
  Taper.integral_phiHatR_sq_mul_sq_le hP.taper hP.one_le_w hwL
theorem integrable_PhiR_sq_mul_sq : Integrable (fun x => P.PhiR T x ^ 2 * x ^ 2) :=
  Taper.integrable_PhiR_sq_mul_sq hP.taper hP.one_le_w hwL
theorem integral_PhiR_sq_mul_sq_le : ∫ x, P.PhiR T x ^ 2 * x ^ 2 ≤ 8 + 2 * (P.crho / P.w) ^ 2 :=
  Taper.integral_PhiR_sq_mul_sq_le hP.taper hP.one_le_w hwL

/-! #### [eq:gbounds] -/
theorem g_ge (y : ℝ) : max (P.L T - 2 * P.w - |y|) 0 ≤ P.g T y :=
  Taper.g_ge hP.taper (w_pos hP) (two_w_le hwL hP) y
theorem g_le_Aphi (y : ℝ) : P.g T y ≤ P.Aphi T y :=
  Taper.g_le_Aphi hP.taper (w_pos hP) (two_w_le hwL hP) y
theorem Aphi_le (y : ℝ) : P.Aphi T y ≤ max (P.L T - |y|) 0 :=
  Taper.Aphi_le hP.taper (w_pos hP) (two_w_le hwL hP) y

/-! #### [eq:psidef] division-free, and ψ form -/
theorem abs_phiHatR_le_L (r : ℝ) : |P.phiHatR T r| ≤ P.L T :=
  Taper.abs_phiHatR_le_L hP.taper (w_pos hP) (two_w_le hwL hP) r
theorem abs_phiHatR_mul_abs_le (r : ℝ) : |P.phiHatR T r| * |r| ≤ 2 :=
  Taper.abs_phiHatR_mul_abs_le hP.taper (w_pos hP) (two_w_le hwL hP) r
theorem abs_phiHatR_mul_sq_le (r : ℝ) : |P.phiHatR T r| * r ^ 2 ≤ P.crho / P.w :=
  Taper.abs_phiHatR_mul_sq_le hP.taper hP.one_le_w (two_w_le hwL hP) r
theorem abs_PhiR_le_L (r : ℝ) : |P.PhiR T r| ≤ P.L T :=
  Taper.abs_PhiR_le_L hP.taper (w_pos hP) (two_w_le hwL hP) r
theorem abs_PhiR_mul_abs_le (r : ℝ) : |P.PhiR T r| * |r| ≤ 2 :=
  Taper.abs_PhiR_mul_abs_le hP.taper (w_pos hP) (two_w_le hwL hP) r
theorem abs_PhiR_mul_sq_le (r : ℝ) : |P.PhiR T r| * r ^ 2 ≤ P.crho / P.w :=
  Taper.abs_PhiR_mul_sq_le hP.taper hP.one_le_w (two_w_le hwL hP) r
theorem abs_phiHatR_le_psi' (r : ℝ) : |P.phiHatR T r| ≤ P.psi' T r :=
  Taper.abs_phiHatR_le_psi hP.taper hP.one_le_w (two_w_le hwL hP) r
theorem abs_PhiR_le_psi' (r : ℝ) : |P.PhiR T r| ≤ P.psi' T r :=
  Taper.abs_PhiR_le_psi hP.taper hP.one_le_w (two_w_le hwL hP) r

/-! #### [eq:psiints] -/
theorem integral_psi'_Ioi_le :
    ∫ r in Ioi 0, P.psi' T r ≤ 4 + 2 * Real.log (P.crho * P.L T / (4 * P.w)) :=
  Taper.integral_psi_Ioi_le hP.taper hP.one_le_w hwL
theorem integral_psi'_sq_le : ∫ r, P.psi' T r ^ 2 ≤ 8 * P.L T :=
  Taper.integral_psi_sq_le hP.taper hP.one_le_w hwL
theorem psi'_integrable : Integrable (P.psi' T) := Taper.psi_integrable hP.taper hP.one_le_w hwL
theorem psi'_sq_integrable : Integrable (fun r => P.psi' T r ^ 2) :=
  Taper.psi_sq_integrable hP.taper hP.one_le_w hwL


end

end Params

end Zeta23
end

-- from Zeta23.PrimeSideA.Bridge
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
  Part of the Zeta23 formalization of the paper
  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/

/-!
# Bridge: the concrete taper data satisfy the abstract prime-side hypotheses `LocalHyps`

The §5 layer (`Zeta23/PrimeSideA.lean`) is proved for abstract data
`p : Setting = (T, λ, w)`, `F : LocalFun = (φ̂, Φ, A_φ, g, a, b)` under `LocalHyps cϱ p F` — the list
of test-family facts [eq:psidef], [eq:psiints], [eq:abdef], [eq:gbounds], [eq:PhigA], [eq:Phi2FT],
[lem:poisson], [eq:PiPfacts] used in §5.  Here:

* `localHyps_concrete` — every `LocalHyps` field for the concrete data, from `Taper.lean`,
  `Poisson.lean` ([lem:poisson]) and `PiFacts.lean`, with
  `cϱ := P.crho = c_ϱ` [eq:phinorms]; hence `localHypsEventually : LocalHypsEventually P.crho P`;
(The instantiation `Params.toSetting / localFun` itself lives in `Zeta23/PrimeSideB/Concrete.lean`.)
-/

noncomputable section

open Real Filter Topology MeasureTheory
open scoped BigOperators ArithmeticFunction

namespace Zeta23

namespace PrimeSide

/-! ## The concrete data satisfy `LocalHyps` -/

/-- The guarded majorant `psiA` [eq:psidef] on the concrete data is Taper's `P.psi' T`
(= Defs' `P.psi T`). -/
lemma psiA_concrete (P : Params) (T : ℝ) : psiA P.crho (P.toSetting T) = P.psi' T := by
  funext r; rfl



end PrimeSide

end Zeta23

end
open Real Filter Topology MeasureTheory
open scoped BigOperators ArithmeticFunction
open Zeta23
open PrimeSide

theorem solution {P : Params} (hP : P.Valid) {T : ℝ} (hwL : 8 * P.w ≤ P.L T)
    (hl : 1 ≤ l T) (hX : 1 ≤ P.X T) : LocalHyps P.crho (P.toSetting T) (P.localFun T) where
  four_le_cϱ := by rw [Params.crho_eq]; exact Taper.four_le_cRho hP.taper
  lam_pos := hP.lam_pos
  lam_le_one := hP.lam_le_one
  one_le_w := hP.one_le_w
  w_le := by show P.w ≤ P.L T / 8; linarith
  one_le_l := hl
  phiHat_cont := Params.phiHatR_continuous hP hwL
  phiHat_even := fun r => Params.phiHatR_even r
  phiHat_le_L := Params.abs_phiHatR_le_L hP hwL
  phiHat_le_inv := Params.abs_phiHatR_mul_abs_le hP hwL
  phiHat_le_sq := Params.abs_phiHatR_mul_sq_le hP hwL
  phiHat_sq_integrable := Params.integrable_phiHatR_sq hP hwL
  phiHat_sq_mul_abs_integrable := Params.integrable_phiHatR_sq_mul_abs hP hwL
  integral_phiHat_sq_mul_abs_le := Params.integral_phiHatR_sq_mul_abs_le hP hwL
  phiHat_sq_mul_sq_integrable := Params.integrable_phiHatR_sq_mul_sq hP hwL
  integral_phiHat_sq_mul_sq_le := Params.integral_phiHatR_sq_mul_sq_le hP hwL
  phiHat_sq_integral := Params.integral_phiHatR_sq hP hwL
  phiHat_sq_fourier := Params.integral_phiHatR_sq_mul_cos hP hwL
  g_lower := Params.g_ge hP hwL
  g_le_Aphi := Params.g_le_Aphi hP hwL
  Aphi_le := Params.Aphi_le hP hwL
  Phi_contDiff := Params.PhiR_contDiff_one hP hwL
  Phi_even := fun r => Params.PhiR_even r
  Phi_le_L := Params.abs_PhiR_le_L hP hwL
  Phi_le_inv := Params.abs_PhiR_mul_abs_le hP hwL
  Phi_le_sq := Params.abs_PhiR_mul_sq_le hP hwL
  Phi_sq_integrable := Params.integrable_PhiR_sq hP hwL
  Phi_sq_mul_abs_integrable := Params.integrable_PhiR_sq_mul_abs hP hwL
  integral_Phi_sq_mul_abs_le := Params.integral_PhiR_sq_mul_abs_le hP hwL
  Phi_sq_mul_sq_integrable := Params.integrable_PhiR_sq_mul_sq hP hwL
  integral_Phi_sq_mul_sq_le := Params.integral_PhiR_sq_mul_sq_le hP hwL
  Phi_zero := Params.PhiR_zero hP hwL
  Phi_sq_integral := Params.integral_PhiR_sq hP hwL
  Phi_sq_fourier := Params.integral_PhiR_sq_mul_cos hP hwL
  poisson := Params.hasSum_phiHatR_mul hP hwL
  b_lower := Params.one_sub_le_b hP hwL
  b_le_a := Params.b_le_a hP hwL
  a_le_one := Params.a_le_one hP hwL
  PiX_cont := PiX_continuous (Real.exp_pos _)
  PiX_bound := PiX_abs_le hX
  psi_integrable := by rw [psiA_concrete]; exact Params.psi'_integrable hP hwL
  psi_sq_integrable := by simpa only [psiA_concrete] using Params.psi'_sq_integrable hP hwL
  integral_psi_Ioi_le := by
    simpa only [psiA_concrete, Params.toSetting_L, Params.toSetting_w] using
      Params.integral_psi'_Ioi_le hP hwL
  integral_psi_sq_le := by
    simpa only [psiA_concrete, Params.toSetting_L] using Params.integral_psi'_sq_le hP hwL
  phiHat_le_psi := by
    simpa only [psiA_concrete, Params.localFun_phiHat] using Params.abs_phiHatR_le_psi' hP hwL
  Phi_le_psi := by
    simpa only [psiA_concrete, Params.localFun_Phi] using Params.abs_PhiR_le_psi' hP hwL
