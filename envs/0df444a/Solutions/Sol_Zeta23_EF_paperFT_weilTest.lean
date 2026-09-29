-- Prove2me | solution 1 for Zeta23.EF.paperFT_weilTest
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T07:49:31.599148+00:00
-- url     : https://prove2.me/submissions/1f0ad0f8-cdd2-4557-bce9-04bbe3900760

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

theorem cintegral_const_mul (c : ℂ) (f : ℝ → ℂ) : ∫ x, c * f x = c * ∫ x, f x :=
  integral_const_mul c f

theorem cintegral_mul_const (c : ℂ) (f : ℝ → ℂ) : ∫ x, f x * c = (∫ x, f x) * c :=
  integral_mul_const c f

theorem cintegral_conj (f : ℝ → ℂ) : ∫ x, conj (f x) = conj (∫ x, f x) := integral_conj

/-! ## Dictionary with Mathlib's Fourier transform -/




/-! ## The test function k = f ⋆ g̃ -/

theorem continuous_tilde {g : ℝ → ℂ} (hg : Continuous g) : Continuous (tilde g) :=
  Complex.continuous_conj.comp (hg.comp continuous_neg)

theorem hasCompactSupport_tilde {g : ℝ → ℂ} (hgs : HasCompactSupport g) :
    HasCompactSupport (tilde g) :=
  (hgs.comp_homeomorph (Homeomorph.neg ℝ)).comp_left (g := fun w : ℂ => conj w) (map_zero _)



theorem paperFT_tilde (g : ℝ → ℂ) (z : ℂ) :
    paperFT (tilde g) z = conj (paperFT g (conj z)) := by
  unfold paperFT tilde
  rw [← cintegral_conj, ← integral_neg_eq_self]
  congr 1; ext u
  simp only [map_mul, ← Complex.exp_conj, conj_conj, Complex.conj_I, Complex.conj_ofReal,
    Complex.ofReal_neg, neg_neg]
  ring_nf





/-! ## App. A: the three identifications -/








/-! ### Pole term: inversion + Fubini, and the two explicit integrals -/
















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

theorem solution {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hfs : HasCompactSupport f) (hgs : HasCompactSupport g) (z : ℂ) :
    paperFT (weilTest f g) z = paperFT f z * conj (paperFT g (conj z)) := by
  rw [← paperFT_tilde]
  have hgt : Continuous (tilde g) := continuous_tilde hg
  have hgts : HasCompactSupport (tilde g) := hasCompactSupport_tilde hgs
  -- the integrand on ℝ × ℝ : (x,t) ↦ f(t) g̃(x−t) e^{izx}, continuous with compact support
  have hFc : Continuous (Function.uncurry fun (x t : ℝ) => f t * tilde g (x - t) * cexp (I * z * x)) := by
    change Continuous fun p : ℝ × ℝ => f p.2 * tilde g (p.1 - p.2) * cexp (I * z * p.1)
    fun_prop
  have hFs : HasCompactSupport
      (Function.uncurry fun (x t : ℝ) => f t * tilde g (x - t) * cexp (I * z * x)) := by
    refine HasCompactSupport.intro ((hgts.isCompact.add hfs.isCompact).prod hfs.isCompact) ?_
    rintro ⟨x, t⟩ hxt
    change f t * tilde g (x - t) * cexp (I * z * x) = 0
    rw [mem_prod, not_and_or] at hxt
    rcases hxt with hx | ht
    · by_cases ht : t ∈ tsupport f
      · have hx' : x - t ∉ tsupport (tilde g) := fun h => hx ⟨x - t, h, t, ht, by ring⟩
        rw [image_eq_zero_of_notMem_tsupport hx']; simp
      · rw [image_eq_zero_of_notMem_tsupport ht]; simp
    · rw [image_eq_zero_of_notMem_tsupport ht]; simp
  have hFi : Integrable (Function.uncurry fun (x t : ℝ) => f t * tilde g (x - t) * cexp (I * z * x))
      (volume.prod volume) := hFc.integrable_of_hasCompactSupport hFs
  -- translation v = x − t in the inner integral
  have hshift : ∀ t : ℝ, ∫ x : ℝ, tilde g (x - t) * cexp (I * z * x)
      = cexp (I * z * t) * ∫ v : ℝ, tilde g v * cexp (I * z * v) := by
    intro t
    rw [← cintegral_const_mul,
      ← integral_sub_right_eq_self (fun v : ℝ => cexp (I * z * t) * (tilde g v * cexp (I * z * v))) t]
    congr 1; ext x
    simp only [Complex.ofReal_sub]
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2; ring
  calc paperFT (weilTest f g) z
      = ∫ x : ℝ, (∫ t : ℝ, f t * tilde g (x - t)) * cexp (I * z * x) := by
        simp only [paperFT, weilTest, convolution_def, ContinuousLinearMap.mul_apply']
    _ = ∫ x : ℝ, ∫ t : ℝ, f t * tilde g (x - t) * cexp (I * z * x) := by
        congr 1; ext x; rw [← cintegral_mul_const]
    _ = ∫ t : ℝ, ∫ x : ℝ, f t * tilde g (x - t) * cexp (I * z * x) := integral_integral_swap hFi
    _ = ∫ t : ℝ, f t * cexp (I * z * t) * ∫ v : ℝ, tilde g v * cexp (I * z * v) := by
        congr 1; ext t
        rw [show (fun x : ℝ => f t * tilde g (x - t) * cexp (I * z * x))
            = fun x => f t * (tilde g (x - t) * cexp (I * z * x)) from funext fun _ => mul_assoc _ _ _,
          cintegral_const_mul, hshift t]
        ring
    _ = paperFT f z * paperFT (tilde g) z := by
        simp only [paperFT]; rw [← cintegral_mul_const]
