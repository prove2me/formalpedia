-- Prove2me | solution 1 for Zeta23.PrimeSide.abs_gkl_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T05:27:41.513028+00:00
-- url     : https://prove2.me/submissions/9f5eec18-6f0e-4151-864d-48593f330175

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
import Theorems.Thm_Zeta23_PrimeSide_abs_phiHat_shift_le

-- from Zeta23.PrimeSideA.EndsCore
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — prime side, [lem:ends] "End effects" (§5, §5.3 of the paper), with [eq:Kdef],
[eq:trG2int], [eq:Kbounds].

TARGET (consumed by thm:traces):
  theorem lem_ends (hΓ : GammaFacts) (hcheb : ChebyshevMertens) (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAt cϱ lam (fun p F =>
      |trGt2A p F - MtotalA p F| ≤ C * (p.L * p.l * Real.log p.l * (p.l ^ 2 + p.X)))

PAPER (§5.3, verbatim): "For T ≥ T₀,  tr G̃² = 𝓜 + O(L l log l (l² + X)),
  𝓜 := ∬_{I×I} Φ(τ−τ')² ν_X(τ) ν_X(τ') dτ dτ'."

ROUTE (paper's, §5.3, with two simplifications that only change absolute constants):
* [eq:trG2int]  L² tr G̃² = Σ_{k,l<d} G_{kl}² = ∬_{ℝ²} K(τ,τ')² ν(τ)ν(τ') dτdτ',
  K(τ,τ') := Σ_{0≤k<d} φ̂(τ−τ_k)φ̂(τ'−τ_k) [eq:Kdef]  — here a product of two integrals and a
  FINITE sum, so no Fubini beyond ∫(f)·∫(g) = ∬ f⊗g.
* K_∞ := Σ_{k∈ℤ} φ̂(τ−τ_k)φ̂(τ'−τ_k) = L Φ(τ−τ') by [lem:poisson] (LocalHyps.poisson), so
  ∬_{I×I} K_∞² νν' = L² 𝓜, and  L²(tr G̃² − 𝓜)·L² … precisely:
  Σ G² − L²𝓜·… = 𝓔₁ + 𝓔₂,  𝓔₁ := ∬_{I×I}(K² − K_∞²)νν',  𝓔₂ := ∬_{ℝ²∖I×I} K²νν'.
* [eq:Kbounds]  |K|, |K_∞| ≤ L² (paper: aL²; a ≤ 1);  |K_out| = |K_∞ − K| handled by the
  weighted AM–GM  |Σ_{k∉[0,d)} a_k b_k| ≤ ½(s ρ(τ) + ρ(τ')/s), ρ(τ) := Σ_{k∉[0,d)} φ̂(τ−τ_k)²
  = aL² − Σ_{k<d} φ̂(τ−τ_k)² (Poisson diagonal — a FINITE expression), with s := g(τ')/g(τ),
  g := (1 + dist(·,∂I))⁻².  This replaces the paper's (∫_I ψ_k)²-sum (§5.3) and gives
  |𝓔₁| ≤ 2L²B²(∫_I ρ/g)(∫_I g) ≪ L²B²·L·l ≤ L³B² l log l  — within the lemma's error (the paper
  gets L³B² log L here; the slack l is free since 𝓔₂ is the dominant term anyway).
* 𝓔₂ exactly as the paper (§5.3): |𝓔₂| ≤ 2L² Σ_{k<d}(∫_{I^c}ψ_k|ν|)(∫_ℝ ψ_k|ν|),
  second factor ≤ 3Ψ₀B, Σ_k first factor = ∫_{I^c}|ν|σ ≪ BLl via the grid bound
  σ(τ) ≤ ψ(Δ) + h⁻¹∫_Δ^∞ψ, σ ≤ d ψ(Δ); for the far range we use log⁺x ≤ 2√x instead of
  integrating logarithms (constants only).
* [eq:Bdef] |ν_X(τ)| ≤ B + log⁺(|τ|/4T), B = l + 4√X: Zeta23/PiFacts.lean
  (from H-Γ + H-cheb); B² ≤ 2l² + 32X.
All constants C may depend on c_ϱ and λ (PrimeSideA convention); T₀ likewise.

FILE LAYOUT:
  EndsCore.lean (this file) — defs, continuity/integrability, [eq:trG2int],
     decomposition, ψ toolkit, [eq:Kbounds] pointwise;
  EndsE1.lean — calE1_bound;   EndsE2.lean (1-D estimates N1/N2 in EndsNu.lean,
     weights in EndsWeighted.lean) — calE2_bound;
  Ends.lean — assembly lem_ends' / lem_ends (proved from the two bounds).
-/

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators

namespace Zeta23
namespace PrimeSide

/-! The ψ majorant `psiA cϱ p r = min(L, 2/|r|, c_ϱ/(w r²))` [eq:psidef] and the [eq:psiints]
facts (psi_integrable, psi_sq_integrable, integral_psi_Ioi_le, integral_psi_sq_le, phiHat_le_psi,
Phi_le_psi) are in Zeta23/PrimeSideA (`LocalHyps`). -/



variable {cϱ : ℝ} (p : Setting) (F : LocalFun) (ν : ℝ → ℝ)

/-! ν-GENERIC LAYER (for Theorem E): every object below that involves the density is
stated for an ABSTRACT `ν : ℝ → ℝ` (hypotheses: `Continuous ν` and `NuBound p B ν` for a free
`B ≥ 0`); ζ is the instantiation `ν := Zeta23.nuX p.X`, `B := Bconst p` (bridges by `rfl`). -/





/-! ## [eq:Kdef] -/




/-! All double integrals below are integrals over `ℝ × ℝ` w.r.t. `volume` (= `volume.prod
volume`), restricted to `I ×ˢ I` or its complement where indicated — the same spelling as
`Mform` in Zeta23/PrimeSideA/Defs.lean. -/






variable {p F ν}

section Structure
variable {B : ℝ}
/-! ## [eq:trG2int] and the decomposition -/







/-! ### Integrability ("the interchange being justified by absolute convergence", §5.3) -/

/-- `|φ̂(r)|(1 + r²) ≤ L + c_ϱ/w` (from [eq:psidef]). -/
theorem abs_phiHat_mul_one_add_sq_le (hF : LocalHypsCoreW cϱ p F) (r : ℝ) :
    |F.phiHat r| * (1 + r ^ 2) ≤ p.L + cϱ / p.w := by
  have h1 := hF.phiHat_le_L r
  have h2 := hF.phiHat_le_sq r
  nlinarith [abs_nonneg (F.phiHat r)]




/-- `log⁺ x ≤ x` for `x ≥ 0`. -/
theorem max_log_zero_le {x : ℝ} (hx : 0 ≤ x) : max (Real.log x) 0 ≤ x := by
  rcases eq_or_lt_of_le hx with h | h
  · rw [← h]; simp
  · exact max_le (by linarith [Real.log_le_sub_one_of_pos h]) hx


/-- crude global form of [eq:Bdef]: `|ν_X(τ)| ≤ B + |τ|` (for `T ≥ 1/4`). -/
theorem abs_nuX_le_linear (hν : NuBound p B ν) (hT : 1 ≤ p.T) (τ : ℝ) :
    |ν τ| ≤ B + |τ| := by
  have h := hν τ
  have h2 : max (Real.log (|τ| / (4 * p.T))) 0 ≤ |τ| / (4 * p.T) := max_log_zero_le (by positivity)
  have h3 : |τ| / (4 * p.T) ≤ |τ| := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [abs_nonneg τ]
  linarith











end Structure

section PsiToolkit
/-! ## ψ toolkit  (generic facts about `psiA cϱ p` = min(L, 2/|r|, c/(w r²)) [eq:psidef]).
Statements are consumed by EndsE1/EndsE2. -/
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}























end PsiToolkit

section Kbounds
/-! ## [eq:Kbounds] pointwise (§5.3) -/
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}









/-! ### K_out pointwise (weighted AM–GM), for 𝓔₁ -/





end Kbounds


end PrimeSide
end Zeta23
end
open MeasureTheory Real Set Finset
open scoped BigOperators
open Zeta23
open PrimeSide
variable {cϱ : ℝ} (p : Setting) (F : LocalFun) (ν : ℝ → ℝ)
variable {p F ν}
variable {B : ℝ}

theorem solution (hF : LocalHypsCoreW cϱ p F) (hν : NuBound p B ν) (hT : 1 ≤ p.T) (hB : 0 ≤ B)
    (k l : ℤ) (τ : ℝ) :
    |gkl p F ν k l τ| ≤ (4 * (p.L + cϱ / p.w) ^ 2 * (1 + p.tau k ^ 2) * (1 + p.tau l ^ 2)
      * (B + 1)) * (1 + τ ^ 2)⁻¹ := by
  have hM : 0 ≤ p.L + cϱ / p.w := by
    have := abs_phiHat_mul_one_add_sq_le hF 0; nlinarith [abs_nonneg (F.phiHat 0)]
  have ha := abs_phiHat_shift_le hF τ (p.tau k)
  have hb := abs_phiHat_shift_le hF τ (p.tau l)
  have hn := abs_nuX_le_linear hν hT τ
  have hpos : 0 < 1 + τ ^ 2 := by positivity
  -- (B + |τ|) ≤ (B + 1)(1 + τ²)
  have hlin : B + |τ| ≤ (B + 1) * (1 + τ ^ 2) := by
    have : |τ| ≤ 1 + τ ^ 2 := by
      rcases le_or_gt |τ| 1 with h | h
      · nlinarith [sq_nonneg τ]
      · have : |τ| ≤ |τ| ^ 2 := by nlinarith
        rw [sq_abs] at this; linarith
    nlinarith
  unfold gkl
  rw [abs_mul, abs_mul]
  have hn' : |ν τ| ≤ (B + 1) * (1 + τ ^ 2) := le_trans hn hlin
  calc |F.phiHat (τ - p.tau k)| * |F.phiHat (τ - p.tau l)| * |ν τ|
      ≤ (2 * (p.L + cϱ / p.w) * (1 + p.tau k ^ 2) / (1 + τ ^ 2))
        * (2 * (p.L + cϱ / p.w) * (1 + p.tau l ^ 2) / (1 + τ ^ 2))
        * ((B + 1) * (1 + τ ^ 2)) := by
        apply mul_le_mul (mul_le_mul ha hb (abs_nonneg _) (by positivity)) hn' (abs_nonneg _)
          (by positivity)
    _ = _ := by field_simp; ring
