-- Prove2me | solution 1 for Zeta23.EF.integral_EL_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T07:56:27.623765+00:00
-- url     : https://prove2.me/submissions/b5d34ce6-c904-44d7-9a72-61b0a4ff19bb

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




/-! ## The test function k = f ⋆ g̃ -/










/-! ## App. A: the three identifications -/








/-! ### Pole term: inversion + Fubini, and the two explicit integrals -/





theorem half_add_I_mul_ne_zero (τ : ℝ) : (1 / 2 : ℂ) + I * τ ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp at this

theorem half_sub_I_mul_ne_zero (τ : ℝ) : (1 / 2 : ℂ) - I * τ ≠ 0 := by
  intro h; have := congrArg Complex.re h; simp at this







/-- `X^s = e^{Ls}` for `X = e^L`. -/
theorem exp_cpow (L : ℝ) (s : ℂ) : ((Real.exp L : ℝ) : ℂ) ^ s = cexp (L * s) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos L).ne'),
    ← Complex.ofReal_log (Real.exp_pos L).le, Real.log_exp]



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

theorem solution (τ : ℝ) {L : ℝ} (hL : 0 < L) :
    ∫ u : ℝ, EL L u * cexp (-I * τ * u)
      = ((2 * ((((Real.exp L : ℝ) : ℂ) ^ ((1 / 2 : ℂ) + I * τ) - 1) / ((1 / 2 : ℂ) + I * τ)).re : ℝ) : ℂ) := by
  set s : ℂ := 1 / 2 + I * τ with hs
  have hs0 : s ≠ 0 := half_add_I_mul_ne_zero τ
  have hsc : conj s = 1 / 2 - I * τ := by
    rw [hs, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, map_div₀, map_one, map_ofNat]
    ring
  have hsc0 : conj s ≠ 0 := by rw [hsc]; exact half_sub_I_mul_ne_zero τ
  -- to a set integral, then an interval integral, then split at 0
  have hind : (fun u : ℝ => EL L u * cexp (-I * τ * u))
      = (Icc (-L) L).indicator (fun u => (Real.exp (|u| / 2) : ℂ) * cexp (-I * τ * u)) := by
    ext u; simp only [EL, Set.indicator_mul_left]
  rw [hind, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -L ≤ L)]
  have hcont : Continuous fun u : ℝ => (Real.exp (|u| / 2) : ℂ) * cexp (-I * τ * u) := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have e1 : EqOn (fun u : ℝ => (Real.exp (|u| / 2) : ℂ) * cexp (-I * τ * u))
      (fun u => cexp (-s * u)) (uIcc (-L) 0) := by
    intro u hu
    rw [uIcc_of_le (by linarith)] at hu
    simp only [abs_of_nonpos hu.2, Complex.ofReal_exp, ← Complex.exp_add, hs]
    congr 1; push_cast; ring
  have e2 : EqOn (fun u : ℝ => (Real.exp (|u| / 2) : ℂ) * cexp (-I * τ * u))
      (fun u => cexp (conj s * u)) (uIcc 0 L) := by
    intro u hu
    rw [uIcc_of_le hL.le] at hu
    simp only [abs_of_nonneg hu.1, Complex.ofReal_exp, ← Complex.exp_add, hsc]
    congr 1; push_cast; ring
  rw [intervalIntegral.integral_congr e1, intervalIntegral.integral_congr e2,
    integral_exp_mul_complex (neg_ne_zero.mpr hs0), integral_exp_mul_complex hsc0]
  -- evaluate: z + conj z with z = (X^s - 1)/s
  have hz : (cexp (-s * (0 : ℝ)) - cexp (-s * ((-L : ℝ) : ℂ))) / -s
      = (((Real.exp L : ℝ) : ℂ) ^ s - 1) / s := by
    rw [exp_cpow]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, Complex.ofReal_neg, mul_neg, neg_mul,
      neg_neg]
    rw [mul_comm s L]
    field_simp
    ring
  have hzc : (cexp (conj s * (L : ℝ)) - cexp (conj s * ((0 : ℝ) : ℂ))) / conj s
      = conj ((((Real.exp L : ℝ) : ℂ) ^ s - 1) / s) := by
    rw [exp_cpow, map_div₀, map_sub, map_one, ← Complex.exp_conj, map_mul, Complex.conj_ofReal]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [mul_comm (conj s) L]
  rw [hz, hzc, Complex.add_conj]
