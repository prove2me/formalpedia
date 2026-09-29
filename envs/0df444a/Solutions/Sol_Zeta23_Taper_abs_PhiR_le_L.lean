-- Prove2me | solution 1 for Zeta23.Taper.abs_PhiR_le_L
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T02:26:15.504482+00:00
-- url     : https://prove2.me/submissions/3c735007-7dae-4302-9ea3-fb18aba4c416

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
import Theorems.Thm_Zeta23_Taper_integral_phi_le
import Theorems.Thm_Zeta23_Taper_phi_contDiff
import Theorems.Thm_Zeta23_Taper_phi_support_subset
import Theorems.Thm_Zeta23_norm_paperFT_le

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


theorem phi_nonneg (hϱ : TaperProfile ϱ) (u : ℝ) : 0 ≤ phi ϱ L w u := hϱ.nonneg _

theorem phi_le_one (hϱ : TaperProfile ϱ) (u : ℝ) : phi ϱ L w u ≤ 1 := hϱ.le_one _

/-- `φ(u) = 0` for `|u| ≥ L/2`. -/
theorem phi_eq_zero (hϱ : TaperProfile ϱ) (hw : 0 < w) {u : ℝ} (hu : L / 2 ≤ |u|) :
    phi ϱ L w u = 0 := by
  unfold phi
  apply hϱ.eq_zero
  apply div_nonpos_of_nonpos_of_nonneg <;> linarith



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

-- from Zeta23.Taper.Decay
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



/-- ∫ φ² ≤ L. -/
theorem integral_phi_sq_le (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) :
    ∫ u, (phi ϱ L w u) ^ 2 ≤ L := by
  refine le_trans (integral_mono_of_nonneg (Eventually.of_forall fun u => sq_nonneg _)
    (phi_integrable hϱ hw hwL) (Eventually.of_forall fun u => ?_)) (integral_phi_le hϱ hw hwL)
  have h0 := phi_nonneg hϱ (L := L) (w := w) u
  have h1 := phi_le_one hϱ (L := L) (w := w) u
  nlinarith


theorem abs_PhiR_le_norm (r : ℝ) : |PhiR ϱ L w r| ≤ ‖Phi ϱ L w r‖ :=
  Complex.abs_re_le_norm _















/-! #### Measurability / integrability of ψ -/














/-! ### [eq:psiints].  We record upper bounds — every downstream citation of [eq:psiints] in §5 is
"≪ log L" or "≤ 8L".  (Paper: "a direct computation (split at |r| = 2/L and |r| = c_ϱ/2w; note
c_ϱ L/4w ≥ 1 by [eq:wrange]) gives Ψ₀ = 4 + 2 log(c_ϱ L/4w), ∫ψ²|r| = 8 + 8 log(c_ϱ L/4w),
∫ψ² ≤ 8L".) -/









/-! #### Generic moment bounds from |F| ≤ ψ-type information -/














end Psi


end Taper

end Zeta23
open Complex MeasureTheory Real Set Filter Topology
open scoped FourierTransform
open Zeta23
open Taper
variable {ϱ : ℝ → ℝ} {L w : ℝ}

theorem solution (hϱ : TaperProfile ϱ) (hw : 0 < w) (hwL : 2 * w ≤ L) (r : ℝ) :
    |PhiR ϱ L w r| ≤ L := by
  refine (abs_PhiR_le_norm r).trans ?_
  have hint : Integrable (fun u => (((phi ϱ L w u) ^ 2 : ℝ) : ℂ)) :=
    ((phiSqC_contDiff hϱ hw hwL).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_of_support_subset_abs (phiSqC_support hϱ hw)))
  have h := norm_paperFT_le hint (phiSqC_support hϱ hw) (r : ℂ)
  simp only [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_im, abs_zero, zero_mul,
    Real.exp_zero, one_mul] at h
  refine h.trans ?_
  calc ∫ u, |phi ϱ L w u ^ 2| = ∫ u, phi ϱ L w u ^ 2 := by
        congr 1 with u; exact abs_of_nonneg (sq_nonneg _)
    _ ≤ L := integral_phi_sq_le hϱ hw hwL
