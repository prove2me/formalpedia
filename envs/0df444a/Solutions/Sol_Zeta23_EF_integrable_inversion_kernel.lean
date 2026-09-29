-- Prove2me | solution 1 for Zeta23.EF.integrable_inversion_kernel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T07:57:11.562555+00:00
-- url     : https://prove2.me/submissions/f8a57caa-c93f-4417-b410-7c3128f33c50

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










/-! ## App. A: the three identifications -/








/-! ### Pole term: inversion + Fubini, and the two explicit integrals -/

theorem norm_cexp_neg_I_mul (τ u : ℝ) : ‖cexp (-I * τ * u)‖ = 1 := by
  rw [Complex.norm_exp]; simp















/-! ### Integrability of the three densities against h (from the computations above) -/





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

theorem solution {k : ℝ → ℂ} (hFk : Integrable (𝓕 k)) {E : ℝ → ℂ}
    (hE : Integrable E) :
    Integrable (Function.uncurry fun (u τ : ℝ) => paperFT k τ * cexp (-I * τ * u) * E u)
      (volume.prod volume) := by
  have hG : Integrable (fun p : ℝ × ℝ => E p.1 * paperFT k p.2) (volume.prod volume) :=
    hE.mul_prod (integrable_paperFT_ofReal hFk)
  refine hG.norm.mono' ?_ ?_
  · have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => paperFT k p.2) (volume.prod volume) :=
      (integrable_paperFT_ofReal hFk).aestronglyMeasurable.comp_snd
    have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ => E p.1) (volume.prod volume) :=
      hE.aestronglyMeasurable.comp_fst
    have h3 : AEStronglyMeasurable (fun p : ℝ × ℝ => cexp (-I * p.2 * p.1)) (volume.prod volume) :=
      (by fun_prop : Continuous fun p : ℝ × ℝ => cexp (-I * p.2 * p.1)).aestronglyMeasurable
    exact (h1.mul h3).mul h2
  · filter_upwards with p
    simp only [Function.uncurry, norm_mul, norm_cexp_neg_I_mul, mul_one]
    exact le_of_eq (mul_comm _ _)
