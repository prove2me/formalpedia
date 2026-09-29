-- Prove2me | solution 1 for Zeta23.WeilEF.differentiableAt_GammaR
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T00:50:22.616186+00:00
-- url     : https://prove2.me/submissions/5fc1dec2-7962-4d0e-89ad-721f2035aeeb

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_Statement

-- from Zeta23.WeilEF.XiLogDeriv
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/XiLogDeriv.lean
The completed zeta function Λ = completedRiemannZeta: log-derivative decomposition, functional equation
for logDeriv, zeros in the strip = nontrivial zeros of ζ with equal analytic order.

Mathlib normalization (verified): for s ≠ 0, riemannZeta s = completedRiemannZeta s / Gammaℝ s
(riemannZeta_def_of_ne_zero) and Gammaℝ s ≠ 0 for 0 < Re s (Gammaℝ_ne_zero_of_re_pos); hence on the
open right half-plane Λ = Γℝ · ζ on the nose (completedZeta_eventuallyEq_mul) — no pole bookkeeping is
needed for the three statements below (Λ's poles at 0, 1 are excluded by hypothesis).
-/

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex Filter Topology








end WeilEF
end Zeta23
end
open Zeta23
open Complex Filter Topology

theorem solution {s : ℂ} (hs : 0 < s.re) : DifferentiableAt ℂ Gammaℝ s := by
  have h1 : DifferentiableAt ℂ (fun u : ℂ => (Real.pi : ℂ) ^ (-u / 2)) s :=
    (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow
      (Or.inl (ofReal_ne_zero.mpr Real.pi_ne_zero))
  have h2 : DifferentiableAt ℂ (fun u : ℂ => Gamma (u / 2)) s := by
    refine (Complex.differentiableAt_Gamma _ fun m hm => ?_).comp s (differentiableAt_id.div_const _)
    have := congrArg Complex.re hm
    simp at this
    have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have : Gammaℝ = fun u : ℂ => (Real.pi : ℂ) ^ (-u / 2) * Gamma (u / 2) := funext Gammaℝ_def
  rw [this]
  exact h1.mul h2
