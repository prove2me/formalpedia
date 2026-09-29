-- Prove2me | solution 1 for Zeta23.PiX_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T06:53:28.53919+00:00
-- url     : https://prove2.me/submissions/af952ffd-624a-4401-9349-afc289b6f261

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Group.Submonoid.BigOperators
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
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

-- from Zeta23.PiFacts
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/PiFacts.lean — [eq:PiPfacts], first clause: the pointwise bound for the
pole density Π_X of [eq:Pidef],

    "|Π_X(τ)| ≤ 3√X/(1+|τ|)"        (the paper, [eq:PiPfacts])

proved here for all X ≥ 1 (the paper applies it with X = e^L → ∞, so any
threshold suffices; no threshold is needed), together with continuity of
Π_X(·) (consumed for integrability).  Consumer: Zeta23/PrimeSideA.lean
(LocalHyps.PiX_bound).

Key inequalities: (1+|τ|)² ≤ 5(1/4+τ²) (so 1/|s| ≤ √5/(1+|τ|) for s = ½+iτ),
|X^s − 1| ≤ √X + 1 ≤ 2√X, and 5/(2π) + 2√5/π < 3.
-/

namespace Zeta23

open Real




/-! ### [eq:Bdef]: the pointwise bound |ν_X(τ)| ≤ B + log⁺(|τ|/4T), B = l + 4√X

Paper (after [eq:deltan]): "We shall use the following pointwise bound for ν_X.
By (eq:mufacts), (eq:PiPfacts) and (eq:cheb1), for T ≥ T₀,
  |ν_X(τ)| ≤ B + log⁺(|τ|/4T)  (τ ∈ ℝ),  |ν_X(τ)| ≤ B  (|τ| ≤ 4T),
  B := l + 4√X,  B² ≪ l² + X."                                        [eq:Bdef]

The μ-part consumes the H-Γ fields, so these lemmas take
hΓ : GammaFacts as a hypothesis — conditional on H-Γ exactly as the paper's §5.
The P_X-part uses the Chebyshev bound Zeta23.Cheb.chebyshevMertens.cheb1b
(paper's literal Σ_{n≤X} Λ(n)/√n ≤ 3√X for X ≥ x₀, absorbed into T₀), so no
Chebyshev hypothesis is needed. -/

section NuBound






end NuBound

end Zeta23
open Zeta23
open Real

theorem solution {X : ℝ} (hX : 1 ≤ X) (τ : ℝ) :
    |PiX X τ| ≤ 3 * Real.sqrt X / (1 + |τ|) := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le one_pos hX
  have hπ : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hπ0 : (0 : ℝ) < Real.pi := by linarith
  have hu : (0 : ℝ) < 1 + |τ| := by positivity
  have hu1 : (1 : ℝ) ≤ 1 + |τ| := by
    have := abs_nonneg τ
    linarith
  have hv : (0 : ℝ) < 1 / 4 + τ ^ 2 := by positivity
  have hq : (1 + |τ|) ^ 2 ≤ 5 * (1 / 4 + τ ^ 2) := by
    nlinarith [sq_nonneg (2 * |τ| - 1 / 2), sq_abs τ, abs_nonneg τ]
  have hsX : (1 : ℝ) ≤ Real.sqrt X := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hX
  have hsX0 : (0 : ℝ) < Real.sqrt X := by linarith
  have hsqrt5 : Real.sqrt 5 ≤ 9 / 4 := by
    rw [Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 9 / 4)]
    norm_num
  have hsqrt5nn : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  set s : ℂ := 1 / 2 + Complex.I * (τ : ℂ) with hs
  have hsre : s.re = 1 / 2 := by simp [hs]
  have hsim : s.im = τ := by simp [hs]
  have hnormsq : ‖s‖ ^ 2 = 1 / 4 + τ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hsre, hsim]
    ring
  have hspos : (0 : ℝ) < ‖s‖ := by
    nlinarith [norm_nonneg s, hnormsq, hv]
  -- the archimedean piece
  have hW : ‖(X : ℂ) ^ s - 1‖ ≤ 2 * Real.sqrt X := by
    have hcpow : ‖(X : ℂ) ^ s‖ = Real.sqrt X := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hX0, hsre, Real.sqrt_eq_rpow]
    calc ‖(X : ℂ) ^ s - 1‖ ≤ ‖(X : ℂ) ^ s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = Real.sqrt X + 1 := by rw [hcpow, norm_one]
      _ ≤ 2 * Real.sqrt X := by linarith
  have husqrt : 1 + |τ| ≤ Real.sqrt 5 * ‖s‖ := by
    have hsq : (1 + |τ|) ^ 2 ≤ (Real.sqrt 5 * ‖s‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5), hnormsq]
      exact hq
    nlinarith [hsq, hu.le, mul_nonneg hsqrt5nn hspos.le]
  -- unfold PiX into the two pieces
  have hPiX : PiX X τ = 1 / (2 * Real.pi * (1 / 4 + τ ^ 2))
      + (1 / Real.pi) * (((X : ℂ) ^ s - 1) / s).re := by
    simp only [PiX, hs]
  -- bound each piece times (1 + |τ|)
  have hAu : |1 / (2 * Real.pi * (1 / 4 + τ ^ 2))| * (1 + |τ|) ≤ 5 / (2 * Real.pi) := by
    rw [abs_of_nonneg (by positivity), div_mul_eq_mul_div, one_mul,
      div_le_div_iff₀ (by positivity) (by positivity)]
    have hu5v : 1 + |τ| ≤ 5 * (1 / 4 + τ ^ 2) := by nlinarith [hq, hu1]
    nlinarith [mul_nonneg hπ0.le (sub_nonneg.mpr hu5v)]
  have hBu : |(1 / Real.pi) * (((X : ℂ) ^ s - 1) / s).re| * (1 + |τ|)
      ≤ 2 * Real.sqrt 5 * Real.sqrt X / Real.pi := by
    have hrew : |(((X : ℂ) ^ s - 1) / s).re| ≤ ‖(X : ℂ) ^ s - 1‖ / ‖s‖ := by
      calc |(((X : ℂ) ^ s - 1) / s).re| ≤ ‖((X : ℂ) ^ s - 1) / s‖ :=
            Complex.abs_re_le_norm _
        _ = ‖(X : ℂ) ^ s - 1‖ / ‖s‖ := norm_div _ _
    have hcore : |(((X : ℂ) ^ s - 1) / s).re| * (1 + |τ|)
        ≤ 2 * Real.sqrt X * Real.sqrt 5 := by
      calc |(((X : ℂ) ^ s - 1) / s).re| * (1 + |τ|)
          ≤ (‖(X : ℂ) ^ s - 1‖ / ‖s‖) * (1 + |τ|) :=
            mul_le_mul_of_nonneg_right hrew hu.le
        _ ≤ (‖(X : ℂ) ^ s - 1‖ / ‖s‖) * (Real.sqrt 5 * ‖s‖) := by
            have hfrac : (0 : ℝ) ≤ ‖(X : ℂ) ^ s - 1‖ / ‖s‖ := by positivity
            exact mul_le_mul_of_nonneg_left husqrt hfrac
        _ = ‖(X : ℂ) ^ s - 1‖ * Real.sqrt 5 := by
            field_simp
        _ ≤ (2 * Real.sqrt X) * Real.sqrt 5 :=
            mul_le_mul_of_nonneg_right hW hsqrt5nn
        _ = 2 * Real.sqrt X * Real.sqrt 5 := by ring
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / Real.pi), mul_assoc]
    calc 1 / Real.pi * (|(((X : ℂ) ^ s - 1) / s).re| * (1 + |τ|))
        ≤ 1 / Real.pi * (2 * Real.sqrt X * Real.sqrt 5) :=
          mul_le_mul_of_nonneg_left hcore (by positivity)
      _ = 2 * Real.sqrt 5 * Real.sqrt X / Real.pi := by ring
  -- numeric endgame: 5/(2π) + 2√5√X/π ≤ 3√X
  have hconst : 5 / (2 * Real.pi) + 2 * Real.sqrt 5 * Real.sqrt X / Real.pi
      ≤ 3 * Real.sqrt X := by
    have hinv : Real.pi * Real.pi⁻¹ = 1 := mul_inv_cancel₀ hπ0.ne'
    have hinvpos : (0 : ℝ) < Real.pi⁻¹ := by positivity
    have hinv3 : Real.pi⁻¹ ≤ 1 / 3 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 3)]
      nlinarith [hinv, hπ]
    rw [div_eq_mul_inv, div_eq_mul_inv]
    have e2 : (2 * Real.pi)⁻¹ = 2⁻¹ * Real.pi⁻¹ := by
      rw [mul_inv]
    rw [e2]
    nlinarith [hsqrt5, hsX, hinv3, hinvpos, hsX0,
      mul_nonneg hinvpos.le hsX0.le, mul_le_mul_of_nonneg_right hinv3 hsX0.le]
  -- assemble
  rw [le_div_iff₀ hu, hPiX]
  calc |1 / (2 * Real.pi * (1 / 4 + τ ^ 2))
        + 1 / Real.pi * (((X : ℂ) ^ s - 1) / s).re| * (1 + |τ|)
      ≤ (|1 / (2 * Real.pi * (1 / 4 + τ ^ 2))|
        + |1 / Real.pi * (((X : ℂ) ^ s - 1) / s).re|) * (1 + |τ|) :=
        mul_le_mul_of_nonneg_right (abs_add_le _ _) hu.le
    _ = |1 / (2 * Real.pi * (1 / 4 + τ ^ 2))| * (1 + |τ|)
        + |1 / Real.pi * (((X : ℂ) ^ s - 1) / s).re| * (1 + |τ|) := by ring
    _ ≤ 5 / (2 * Real.pi) + 2 * Real.sqrt 5 * Real.sqrt X / Real.pi := add_le_add hAu hBu
    _ ≤ 3 * Real.sqrt X := hconst
