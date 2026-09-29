-- Prove2me | solution 1 for Zeta23.RvM.logDeriv_GammaR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:52:11.87819+00:00
-- url     : https://prove2.me/submissions/3da920ea-aa4e-47c6-b849-66fc3afe0cdf

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_RvM_Defs
import Definitions.Def_Zeta23_RvM_GammaSide
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_ZetaReflect

-- from Zeta23.RvM.GammaSide
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/RvM/GammaSide.lean — the Γ-factor side of the folded contour is
EXACTLY the paper's ∫μ:  (1/π)·Im ∫_L Γℝ'/Γℝ ds = ∫_{T₁}^{T₂} μ(t) dt  for 0 < T₁,
because Γℝ'/Γℝ is holomorphic on Re s > 0 (Cauchy–Goursat on [½,2]×[T₁,T₂] moves L to the critical-line
segment) and Re Γℝ'/Γℝ(½+it) = ½ Re ψ(¼+it/2) − ½ log π = π·μ(t)  (Γℝ(s) = π^{−s/2}Γ(s/2), μ = Zeta23.mu).
-/

open Complex MeasureTheory Set
open scoped Interval

noncomputable section

namespace Zeta23.RvM



lemma Gamma_half_differentiableAt {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Complex.Gamma (s / 2) := by
  apply Complex.differentiableAt_Gamma
  intro m h
  have := congrArg Complex.re h
  simp at this
  have : (0:ℝ) ≤ m := Nat.cast_nonneg m
  linarith







/-! ### helpers for the assembly -/



end Zeta23.RvM
end
open Complex MeasureTheory Set
open scoped Interval
open Zeta23
open Zeta23.RvM

theorem solution {s : ℂ} (hs : 0 < s.re) :
    logDeriv Complex.Gammaℝ s = -(Real.log Real.pi : ℂ) / 2 + (1/2 : ℂ) * Complex.digamma (s / 2) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e : Complex.Gammaℝ = fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2) := by
    funext s; rw [Complex.Gammaℝ_def]
  have hf : (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) s ≠ 0 := by
    simp only [ne_eq, cpow_eq_zero_iff, hπ, false_and, not_false_eq_true]
  have hg : (fun s : ℂ => Complex.Gamma (s / 2)) s ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m h
    have := congrArg Complex.re h
    simp at this
    have : (0:ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hdf : DifferentiableAt ℂ (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) s :=
    DifferentiableAt.const_cpow (by fun_prop) (Or.inl hπ)
  have hdg : DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (s / 2)) s :=
    (Gamma_half_differentiableAt hs).comp s (by fun_prop)
  rw [e, logDeriv_mul (f := fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) (g := fun s : ℂ => Complex.Gamma (s / 2)) s hf hg hdf hdg]
  -- first factor
  have h1 : logDeriv (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) s = -(Real.log Real.pi : ℂ) / 2 := by
    have hder : HasDerivAt (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2))
        ((Real.pi : ℂ) ^ (-s / 2) * Complex.log Real.pi * (-1 / 2)) s := by
      have : HasDerivAt (fun s : ℂ => -s / 2) (-1 / 2 : ℂ) s := by
        simpa using ((hasDerivAt_id s).neg.div_const (2:ℂ))
      exact this.const_cpow (Or.inl hπ)
    rw [logDeriv_apply, hder.deriv]
    have hne : (Real.pi : ℂ) ^ (-s / 2) ≠ 0 := hf
    rw [Complex.ofReal_log Real.pi_pos.le]
    field_simp
  -- second factor
  have h2 : logDeriv (fun s : ℂ => Complex.Gamma (s / 2)) s = (1/2 : ℂ) * Complex.digamma (s / 2) := by
    have := logDeriv_comp (f := Complex.Gamma) (g := fun s : ℂ => s / 2) (x := s)
      (Gamma_half_differentiableAt hs) (by fun_prop)
    rw [show (Complex.Gamma ∘ fun s : ℂ => s / 2) = fun s => Complex.Gamma (s / 2) from rfl] at this
    rw [this, Complex.digamma_def]
    have : deriv (fun s : ℂ => s / 2) s = 1 / 2 := by
      rw [deriv_div_const, deriv_id'']
    rw [this]; ring
  rw [h1, h2]
