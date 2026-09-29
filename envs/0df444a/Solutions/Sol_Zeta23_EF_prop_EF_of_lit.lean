-- Prove2me | solution 1 for Zeta23.EF.prop_EF_of_lit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T07:48:36.97565+00:00
-- url     : https://prove2.me/submissions/262df2c1-6a6e-4911-b740-811ab4232253

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_ExplicitFormula
import Theorems.Thm_Zeta23_EF_integrable_paperFT_mul_PiX
import Theorems.Thm_Zeta23_EF_literatureRHS_eq_integral_nu
import Theorems.Thm_Zeta23_EF_paperFT_weilTest

-- from Zeta23.ExplicitFormula
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ExplicitFormula.lean  —  the explicit formula, normalisations (paper App. A [app:EF]).

The *normalisation chain*: the passage from a literature-verbatim explicit formula to the paper's
density ν_X = μ + Π_X + P_X [eq:mudef]–[eq:nudef], with every 2π and every sign:

  * `EF.literatureRHS` / `EF_lit` : the right-hand side of [eq:EFstd] (App. A, first display), i.e. the
    Weil explicit formula in the form the paper quotes from [IK04, Thm 5.12] / [Wei52] / [Bom00],
    for a single test function k ∈ C_c²(ℝ) with h(z) := ∫ k(u) e^{izu} du;
  * `EF.prop_EF_of_lit` : [eq:EFstd] for k := f ⋆ g̃  ⟹  [eq:EF]  W(f,g) = ∫ h_f(τ) conj(h_g(τ)) ν_X(τ) dτ,
    X = e^L, for f, g ∈ C_c²(ℝ) supported in [−L/2, L/2]  — exactly App. A's three identifications
    (Gamma term, prime term, pole term) plus h_{f⋆g̃}(z) = h_f(z)·conj(h_g(conj z)).

The truth of [eq:EFstd] itself (contour integration of
h((s-1/2)/i)·ξ'/ξ(s)) is the hypothesis `EF_lit`, stated for the zero configuration
abstractly.

CONVENTIONS (paper [Notation]).  Paper Fourier transform:
    f̂(τ) = h_f(τ) := ∫_ℝ f(u) e^{iτu} du,   inversion  f(u) = (1/2π) ∫_ℝ h_f(r) e^{-iru} dr.
Mathlib: 𝓕 f w = ∫ v, exp(-2πi v w) • f v.  Dictionary (proved below, `paperFT_ofReal_eq_fourier`):
    h_f(τ) = 𝓕 f (-τ/(2π)).
-/

open MeasureTheory Complex Filter Set
open scoped Real FourierTransform Convolution ComplexConjugate ArithmeticFunction

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Zeta23
namespace EF

/-! ### App. A objects owned by this file -/



end EF


namespace EF

/-! ## The literature form [eq:EFstd] -/





/-! ## ℂ-specialised integral helpers

(In this toolchain `rw [← integral_const_mul]` fails to key-match on ℂ-valued integrals because the
RCLike-generic lemma elaborates `Mul ℂ`/`NormedAddCommGroup ℂ` through a different instance path than
a goal written with `*`; restating the lemmas at ℂ (proved by `exact`) makes `rw` usable.) -/




/-! ## Dictionary with Mathlib's Fourier transform -/

/-- `h_k(τ) = 𝓕 k (−τ/(2π))` for real τ. -/
theorem paperFT_ofReal_eq_fourier (k : ℝ → ℂ) (τ : ℝ) :
    paperFT k τ = 𝓕 k (-τ / (2 * π)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  unfold paperFT
  congr 1; ext u
  rw [smul_eq_mul, mul_comm (k u)]
  congr 1
  have : (-2 * π * u * (-τ / (2 * π))) = τ * u := by
    field_simp
  rw [this]
  push_cast
  ring_nf

/-- `h_k` is integrable on the real line when `𝓕 k` is (dictionary + linear substitution). -/
theorem integrable_paperFT_ofReal {k : ℝ → ℂ} (hFk : Integrable (𝓕 k)) :
    Integrable (fun τ : ℝ => paperFT k τ) := by
  have : (fun τ : ℝ => paperFT k τ) = fun τ => (𝓕 k) ((-(1 / (2 * π))) * τ) := by
    ext τ; rw [paperFT_ofReal_eq_fourier, show -(1 / (2 * π)) * τ = -τ / (2 * π) by ring]
  rw [this]
  exact hFk.comp_mul_left' (neg_ne_zero.mpr (by positivity))


/-! ## The test function k = f ⋆ g̃ -/

theorem continuous_tilde {g : ℝ → ℂ} (hg : Continuous g) : Continuous (tilde g) :=
  Complex.continuous_conj.comp (hg.comp continuous_neg)

theorem hasCompactSupport_tilde {g : ℝ → ℂ} (hgs : HasCompactSupport g) :
    HasCompactSupport (tilde g) :=
  (hgs.comp_homeomorph (Homeomorph.neg ℝ)).comp_left (g := fun w : ℂ => conj w) (map_zero _)

theorem support_tilde_subset (g : ℝ → ℂ) : Function.support (tilde g) ⊆ -tsupport g := by
  intro u hu
  simp only [Function.mem_support, tilde, ne_eq, map_eq_zero] at hu
  exact subset_tsupport _ (by simpa [Function.mem_support] using hu)

theorem tsupport_tilde_subset {g : ℝ → ℂ} {L : ℝ} (hgs : tsupport g ⊆ Icc (-(L / 2)) (L / 2)) :
    tsupport (tilde g) ⊆ Icc (-(L / 2)) (L / 2) := by
  refine closure_minimal ((support_tilde_subset g).trans ?_) isClosed_Icc
  intro u hu
  have := hgs hu
  simp only [mem_Icc] at this ⊢
  constructor <;> linarith [this.1, this.2]



theorem weilTest_contDiff {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hg : Continuous g)
    (hfs : HasCompactSupport f) :
    ContDiff ℝ 2 (weilTest f g) := by
  have := hfs.contDiff_convolution_left (n := 2) (L := ContinuousLinearMap.mul ℝ ℂ) (μ := volume)
    hf (continuous_tilde hg).locallyIntegrable
  simpa [weilTest] using this

theorem weilTest_hasCompactSupport {f g : ℝ → ℂ}
    (hfs : HasCompactSupport f) (hgs : HasCompactSupport g) :
    HasCompactSupport (weilTest f g) :=
  hfs.convolution _ (hasCompactSupport_tilde hgs)

/-- App. A: `supp k ⊆ [−L, L]` when `supp f, supp g ⊆ [−L/2, L/2]`. -/
theorem tsupport_weilTest_subset {f g : ℝ → ℂ} {L : ℝ}
    (hfs : tsupport f ⊆ Icc (-(L / 2)) (L / 2)) (hgs : tsupport g ⊆ Icc (-(L / 2)) (L / 2)) :
    tsupport (weilTest f g) ⊆ Icc (-L) L := by
  refine closure_minimal ?_ isClosed_Icc
  refine (support_convolution_subset _).trans ?_
  rintro x ⟨a, ha, b, hb, rfl⟩
  have ha' := hfs (subset_tsupport _ ha)
  have hb' := tsupport_tilde_subset hgs (subset_tsupport _ hb)
  simp only [mem_Icc] at ha' hb' ⊢
  constructor <;> linarith [ha'.1, ha'.2, hb'.1, hb'.2]

/-! ## App. A: the three identifications -/




/-- `h(r) cos(r y)` is integrable in r when h is. -/
theorem integrable_paperFT_mul_cos {k : ℝ → ℂ} (hFk : Integrable (𝓕 k)) (y : ℝ) :
    Integrable (fun r : ℝ => paperFT k r * (Real.cos (r * y) : ℂ)) := by
  refine (integrable_paperFT_ofReal hFk).mul_bdd (c := 1) (by fun_prop) ?_
  filter_upwards with r
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact Real.abs_cos_le_one _




/-! ### Pole term: inversion + Fubini, and the two explicit integrals -/
















/-! ### Integrability of the three densities against h (from the computations above) -/


theorem paperFT_mul_PX_eq (k : ℝ → ℂ) (L : ℝ) :
    (fun τ : ℝ => paperFT k τ * (PX (Real.exp L) τ : ℂ))
      = fun τ : ℝ => ∑ n ∈ Finset.Ioc 0 ⌊Real.exp L⌋₊, (-(1 / π) * ((Λ n / Real.sqrt n : ℝ) : ℂ)) *
          (paperFT k τ * (Real.cos (τ * Real.log n) : ℂ)) := by
  ext τ
  simp only [PX]
  push_cast
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

theorem integrable_paperFT_mul_PX {k : ℝ → ℂ} (L : ℝ) (hFk : Integrable (𝓕 k)) :
    Integrable (fun τ : ℝ => paperFT k τ * (PX (Real.exp L) τ : ℂ)) := by
  rw [paperFT_mul_PX_eq]
  exact integrable_finsetSum _ (fun n _ => (integrable_paperFT_mul_cos hFk _).const_mul _)

/-- `h·ν_X` is integrable, given that `h·μ` is (μ grows like log|τ|, so this last fact needs the
decay [eq:hfbound] of h and the Stirling bound [eq:mufacts]; it is supplied by the caller). -/
theorem integrable_paperFT_mul_nuX {k : ℝ → ℂ} {L : ℝ} (hL : 0 < L) (hFk : Integrable (𝓕 k))
    (hμ : Integrable (fun τ : ℝ => paperFT k τ * (mu τ : ℂ))) :
    Integrable (fun τ : ℝ => paperFT k τ * (nuX (Real.exp L) τ : ℂ)) := by
  refine ((hμ.add (integrable_paperFT_mul_PiX hL hFk)).add (integrable_paperFT_mul_PX L hFk)).congr ?_
  filter_upwards with τ
  simp only [nuX, Pi.add_apply]
  push_cast
  ring

/-! ## Adding up -/


/-! ## [prop:EF] from the literature form -/


end EF
end Zeta23
end
open MeasureTheory Complex Filter Set
open scoped Real FourierTransform Convolution ComplexConjugate ArithmeticFunction
set_option backward.isDefEq.respectTransparency false
open Zeta23
open EF

theorem solution (Z : ZeroConfig) (hEF : EF_lit Z) {L : ℝ} (hL : 0 < L) {f g : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hfs : tsupport f ⊆ Icc (-(L / 2)) (L / 2)) (hgs : tsupport g ⊆ Icc (-(L / 2)) (L / 2))
    (hFk : Integrable (𝓕 (weilTest f g)))
    (hμ : Integrable (fun τ : ℝ => paperFT (weilTest f g) τ * (mu τ : ℂ))) :
    Summable (fun ρ : Z.carrier => Z.Wsummand f g ρ) ∧
    Integrable (fun τ : ℝ => paperFT f τ * conj (paperFT g τ) * (nuX (Real.exp L) τ : ℂ)) ∧
    Z.W f g = ∫ τ : ℝ, paperFT f τ * conj (paperFT g τ) * (nuX (Real.exp L) τ : ℂ) := by
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) hfs
  have hgc : HasCompactSupport g :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport g) hgs
  have hkd : ContDiff ℝ 2 (weilTest f g) := weilTest_contDiff hf hg.continuous hfc
  have hk : Continuous (weilTest f g) := hkd.continuous
  have hks : tsupport (weilTest f g) ⊆ Icc (-L) L := tsupport_weilTest_subset hfs hgs
  obtain ⟨hsum, heq⟩ := hEF (weilTest f g) hkd (weilTest_hasCompactSupport hfc hgc)
  have hfac : ∀ z : ℂ, paperFT (weilTest f g) z = paperFT f z * conj (paperFT g (conj z)) :=
    paperFT_weilTest hf.continuous hg.continuous hfc hgc
  -- termwise: m_ρ h_k(γ_ρ) = m_ρ h_f(γ_ρ) conj(h_g(conj γ_ρ))
  have hterm : (fun ρ : Z.carrier => (Z.mult ρ : ℂ) * paperFT (weilTest f g) (gammaOf ρ))
      = fun ρ : Z.carrier => Z.Wsummand f g ρ := by
    ext ρ; simp only [ZeroConfig.Wsummand, hfac, mul_assoc]
  -- on the real line: h_k(τ) = h_f(τ) conj(h_g(τ))
  have hreal : (fun τ : ℝ => paperFT (weilTest f g) τ * (nuX (Real.exp L) τ : ℂ))
      = fun τ : ℝ => paperFT f τ * conj (paperFT g τ) * (nuX (Real.exp L) τ : ℂ) := by
    ext τ; rw [hfac, Complex.conj_ofReal]
  refine ⟨hterm ▸ hsum, hreal ▸ integrable_paperFT_mul_nuX hL hFk hμ, ?_⟩
  rw [literatureRHS_eq_integral_nu hL hk hks hFk hμ, hreal] at heq
  rw [← heq, ZeroConfig.W, ← hterm]
