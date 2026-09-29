-- Prove2me | solution 1 for Zeta23.PrimeSide.sqrt_shift_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T04:54:43.742784+00:00
-- url     : https://prove2.me/submissions/a0c90941-8b93-4bf5-a69c-52e72c93d873

import Mathlib
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
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs
import Definitions.Def_Zeta23_PrimeSideA_EndsCore

-- from Zeta23.PrimeSideA.EndsWeighted
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/PrimeSideA/EndsWeighted.lean

Substrate for the 𝓔₂ bound [lem:ends], shared with EndsNu.lean (the
1-D estimates N1/N2): log⁺/√ facts, pointwise ν-bounds from NuBound, integrability of the
ψ-weighted ν integrals, and the grid-domination lemmas reducing Σ_{k<d} ψ(τ−τ_k) to
Σ_{j<d} ψ(Δ + jh), Δ = dist(τ, I).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Real Set

namespace Zeta23
namespace PrimeSide
section Prelim

variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}



theorem sqrt_add_le' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  have h : x + y ≤ (Real.sqrt x + Real.sqrt y) ^ 2 := by
    have hx' := Real.sq_sqrt hx
    have hy' := Real.sq_sqrt hy
    nlinarith [mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]
  calc Real.sqrt (x + y) ≤ Real.sqrt ((Real.sqrt x + Real.sqrt y) ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt x + Real.sqrt y := Real.sqrt_sq (by positivity)




end Prelim

section Weighted

variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}





end Weighted

section Grid

variable {cϱ : ℝ} {p : Setting} {F : LocalFun}



end Grid

end PrimeSide
end Zeta23
end
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Real Set
open Zeta23
open PrimeSide
variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}

theorem solution {a r T' : ℝ} (hT : 0 < T') (ha : |a| ≤ 4 * T') :
    Real.sqrt (|a + r| / (4 * T')) ≤ 1 + Real.sqrt (|r| / (4 * T')) := by
  have h1 : |a + r| / (4 * T') ≤ |a| / (4 * T') + |r| / (4 * T') := by
    rw [← add_div]
    gcongr
    exact abs_add_le a r
  calc Real.sqrt (|a + r| / (4 * T'))
      ≤ Real.sqrt (|a| / (4 * T') + |r| / (4 * T')) := Real.sqrt_le_sqrt h1
    _ ≤ Real.sqrt (|a| / (4 * T')) + Real.sqrt (|r| / (4 * T')) :=
        sqrt_add_le' (by positivity) (by positivity)
    _ ≤ 1 + Real.sqrt (|r| / (4 * T')) := by
        gcongr
        rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
        exact Real.sqrt_le_sqrt (by rw [div_le_one (by positivity)]; linarith)
