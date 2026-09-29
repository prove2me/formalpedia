-- Prove2me | solution 1 for Zeta23.PrimeSide.W1d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T05:47:50.962977+00:00
-- url     : https://prove2.me/submissions/c27737f1-7a6b-416e-bee8-850044c8da81

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
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
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
import Definitions.Def_Zeta23_PrimeSideA_EndsE1
import Theorems.Thm_Zeta23_PrimeSide_setIntegral_psiA_sq_Ioi_le_div

-- from Zeta23.PrimeSideA.EndsE1
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — [lem:ends], bound for 𝓔₁ (§5.3).  Statement `calE1_bound` consumed by
Zeta23/PrimeSideA/Ends.lean.

ROUTE.  On I×I: |ν|,|ν'| ≤ B;  |K + K_∞| ≤ 2L² (abs_Kfun_le, abs_Kinf_le);
|K_∞ − K| ≤ (s ρ(τ) + ρ(τ')/s)/2 for every s > 0 (abs_Kinf_sub_Kfun_le), with the choice
s := g(τ')/g(τ), g(τ) := (1 + min(τ−T, 2T−τ))⁻² > 0.  Hence pointwise
  |K²−K_∞²||ν||ν'| ≤ L²B² ( ρ(τ)/g(τ)·g(τ') + g(τ)·ρ(τ')/g(τ') )
and integrating over I×I (product structure):  |𝓔₁| ≤ 2L²B² (∫_I ρ/g)(∫_I g),  ∫_I g ≤ 2.
Pointwise majorant (finite partial sums of the HasSum for ρ, ψ antitone, grid lemma):
  ρ(τ) ≤ W(τ−T) + W(2T−τ) + ψ(τ_d − τ)²,   W(Δ) := ψ(Δ)² + h⁻¹∫_{(Δ,∞)}ψ²,
and 1/g = (1+min(τ−T,2T−τ))² ≤ (1+(τ−T))², (1+(2T−τ))², (1+h+|τ_d−τ|)² respectively, so
  ∫_I ρ/g ≤ 2∫_0^T W(u)(1+u)² du + ∫_ℝ ψ(r)²(2+|r|)² dr ≪ L² + L·l   (split at 1; ψ ≤ L,
  ψ(r) ≤ (c/w)/r², ∫_{(Δ,∞)}ψ² ≤ min(8L, (c/w)²/(3Δ³)), log T ≤ 2l).
Budget: |𝓔₁| ≤ C(c_ϱ)·L²B²(L² + L l) ≤ C·L³B² l (L = λl ≤ l).
-/

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators

namespace Zeta23
namespace PrimeSide

variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}

/-! ### Definitions -/




/-! ### Leaf integrals -/






/-- J(u) := ∫_{(u,∞)} ψ² is antitone in u (ψ² ≥ 0). -/
theorem antitone_setIntegral_psiA_sq_Ioi (hF : LocalHypsCoreW cϱ p F) :
    Antitone (fun u : ℝ => ∫ r in Set.Ioi u, psiA cϱ p r ^ 2) := fun _ _ huv =>
  setIntegral_mono_set hF.psi_sq_integrable.integrableOn
    (Filter.Eventually.of_forall fun _ => sq_nonneg _) (Set.Ioi_subset_Ioi huv).eventuallyLE




/-! ### Pointwise facts on I -/








/-! ### The majorant for ρ on I -/






/-! ### The weight integrals -/



/-! ### Assembly -/

section Bounds
variable (cϱ lam : ℝ)




end Bounds

section BoundsCor
variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}


variable (cϱ lam : ℝ)


end BoundsCor

end PrimeSide
end Zeta23
end
open MeasureTheory Real Set Finset
open scoped BigOperators
open Zeta23
open PrimeSide
variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}

theorem solution (hF : LocalHypsCoreW cϱ p F) (hT : 1 ≤ p.T) :
    ∫ u in (1:ℝ)..p.T, (∫ r in Set.Ioi u, psiA cϱ p r ^ 2) * (1 + u) ^ 2
      ≤ 4 / 3 * (cϱ / p.w) ^ 2 * Real.log p.T := by
  have hJanti := antitone_setIntegral_psiA_sq_Ioi hF
  have h0 : (0:ℝ) ∉ Set.uIcc (1:ℝ) p.T := by
    rw [Set.uIcc_of_le hT]; exact fun h => by linarith [h.1]
  have hint : IntervalIntegrable
      (fun u : ℝ => (∫ r in Set.Ioi u, psiA cϱ p r ^ 2) * (1 + u) ^ 2) volume 1 p.T :=
    hJanti.intervalIntegrable.mul_continuousOn (by fun_prop)
  have hint2 : IntervalIntegrable (fun u : ℝ => 4 / 3 * (cϱ / p.w) ^ 2 * u⁻¹) volume 1 p.T := by
    refine ContinuousOn.intervalIntegrable (continuousOn_const.mul (continuousOn_inv₀.mono ?_))
    intro x hx hx0
    exact h0 (hx0 ▸ hx)
  calc ∫ u in (1:ℝ)..p.T, (∫ r in Set.Ioi u, psiA cϱ p r ^ 2) * (1 + u) ^ 2
      ≤ ∫ u in (1:ℝ)..p.T, 4 / 3 * (cϱ / p.w) ^ 2 * u⁻¹ := by
        refine intervalIntegral.integral_mono_on hT hint hint2 fun u hu => ?_
        have hu0 : 0 < u := by linarith [hu.1]
        have hJu := setIntegral_psiA_sq_Ioi_le_div hF hu0
        have h4 : (1 + u) ^ 2 ≤ 4 * u ^ 2 := by nlinarith [hu.1]
        calc (∫ r in Set.Ioi u, psiA cϱ p r ^ 2) * (1 + u) ^ 2
            ≤ (cϱ / p.w) ^ 2 / (3 * u ^ 3) * (4 * u ^ 2) :=
              mul_le_mul hJu h4 (sq_nonneg _) (by positivity)
          _ = 4 / 3 * (cϱ / p.w) ^ 2 * u⁻¹ := by field_simp
    _ = 4 / 3 * (cϱ / p.w) ^ 2 * Real.log p.T := by
        rw [intervalIntegral.integral_const_mul, integral_inv h0, div_one]
