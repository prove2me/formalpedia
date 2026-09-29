-- Prove2me | solution 1 for Zeta23.PrimeSide.nu_grid_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T04:57:50.914066+00:00
-- url     : https://prove2.me/submissions/98dcf4cc-1ccb-4ff9-ac4f-5522bb4fa464

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
import Definitions.Def_Zeta23_PrimeSideA_EndsNu
import Theorems.Thm_Zeta23_PrimeSide_nu_grid_bound_raw

-- from Zeta23.PrimeSideA.Basic
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization of
  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/


-- Contains: LocalHyps, EventuallyAt, the 𝓜-bilinearity/sup-bound lemmas, the large-T regime
-- lemmas, and all per-grid-point lemmas for [prop:trace].

/-!
# Prime side, part A — paper §5 [sec:prime]:  [prop:trace], [lem:ends], [eq:Msplit], [prop:mumu], [prop:cross]

Seam with `PrimeSideB.lean` ([prop:PP], [thm:traces]): see the header of
`Zeta23/PrimeSideA/Defs.lean`.  Everything here is ζ-free: the zeros never
appear in §5 ("In this section the zeros play no role", §5); `N(T,2T)` enters [prop:trace]
only through [eq:muints] + [eq:RvM], which we take as hypotheses on an abstract real `N`.

## Shape of the results
All error terms are explicit inequalities, uniform in `T`:
  `∃ C, EventuallyAt cϱ lam (fun p F => |lhs p F − main p F| ≤ C * err p)`
where `EventuallyAt cϱ lam P` means: there is `T₀` such that `P p F` holds for every parameter set
`p` with `p.lam = lam`, `T₀ ≤ p.T` and every taper datum `F` satisfying `LocalHyps cϱ p F`.
So `C` and `T₀` may depend on `c_ϱ`, on the constants inside H-Γ/H-cheb, and on `λ` — the paper
has `C` depending on ϱ only and `T₀ = T₀(λ)` (§5.5); ours is the (weaker, sufficient at fixed λ)
reading.  This is a deviation from the paper.

## Hypotheses consumed (all proved elsewhere in the repository; none is a Lean axiom)
* `Zeta23.GammaFacts` (H-Γ [eq:mufacts]+[eq:muints]) and `Zeta23.ChebyshevMertens` (H-cheb
  [lem:cheb]) — Zeta23/Hypotheses.lean, verbatim (fields of `PaperInputs`).
* `LocalHyps cϱ p F` — taper/test-family facts [eq:psidef], [eq:abdef], [eq:gbounds], [eq:Phi2FT],
                      `∫φ̂² = 2πaL`, `Φ(0) = aL`, `∫Φ² = 2πbL`;
                      [lem:poisson] (★); [eq:PiPfacts] for Π_X;
                      parameter regime [eq:wrange], `0<λ≤1`.
-/

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction

namespace Zeta23
namespace PrimeSide

/-! ## Hypothesis packages

H-Γ and H-cheb are Zeta23/Hypotheses.lean's `Zeta23.GammaFacts` and `Zeta23.ChebyshevMertens` (about the
concrete `Zeta23.mu` and Λ-sums), taken verbatim.  The taper/test-family facts are packaged here: -/




/-! ### Bilinearity and symmetry of 𝓜[·,·] (§5.4: "a symmetric bilinear form (Φ² is even)") -/

section MformLemmas
variable {Φ : ℝ → ℝ} {T : ℝ}








end MformLemmas


/-! ### The "insert sup bounds" estimate for 𝓜[·,·]  (§5.4) -/

section SupBound
variable {Φ : ℝ → ℝ} {T : ℝ}



end SupBound


/-! ### The large-T regime: elementary consequences of the hypotheses -/

section Regime
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}


/-- `l ≥ l₀` once `T ≥ 2π e^{l₀}`. -/
lemma Setting.le_l_of_T {p : Setting} {l₀ : ℝ} (hT : 2 * π * Real.exp l₀ ≤ p.T) : l₀ ≤ p.l := by
  have h2π : (0:ℝ) < 2 * π := by positivity
  have h : Real.exp l₀ ≤ p.T / (2 * π) := by rw [le_div_iff₀ h2π]; linarith
  calc l₀ = Real.log (Real.exp l₀) := (Real.log_exp _).symm
    _ ≤ Real.log (p.T / (2 * π)) := Real.log_le_log (Real.exp_pos _) h
    _ = p.l := rfl










/-! ### Window-generic core of the taper hypotheses (paper §7.1 [subsec:MT])

"Nothing in Sections 4–5 used that φ is flat-topped" — except the [eq:gbounds] plateau lower
bound and the [eq:abdef] lower bound on b.  LocalHypsCore is LocalHyps minus exactly those two
facts, with the window-generic replacements g_nonneg and b_ge_half (both hold for the
Montgomery–Taylor window of [thm:D], which does not satisfy LocalHyps).  Surviving field names
are identical to LocalHyps'.  The window-generic §5 results can be re-typed over this
structure; the structure itself is purely additive. -/






/-! Core copies of the LocalHyps helper lemmas (same names under the Core namespace). -/













lemma LocalHypsCoreW.eight_le_L {cϱ : ℝ} {p : Setting} {F : LocalFun}
    (hF : LocalHypsCoreW cϱ p F) : 8 ≤ p.L := by
  linarith [hF.one_le_w, hF.w_le]

lemma LocalHypsCoreW.L_pos {cϱ : ℝ} {p : Setting} {F : LocalFun}
    (hF : LocalHypsCoreW cϱ p F) : 0 < p.L := by
  linarith [hF.eight_le_L]








end Regime

/-! ### Elementary lemmas for [prop:trace] -/

section TraceLemmas




variable {cϱ : ℝ} {p : Setting} {F : LocalFun}




end TraceLemmas

/-! ### Analytic lemmas for [prop:trace]: growth and increments of μ, decay of Π_X -/

section TraceAnalytic
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}






















end TraceAnalytic

end PrimeSide
end Zeta23
end
end

-- from Zeta23.PrimeSideA.EndsNu
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — [lem:ends], the two one-dimensional ν-weighted ψ estimates feeding the 𝓔₂ bound
(§5.3 of the paper).  Consumed by Zeta23/PrimeSideA/EndsE2.lean.

* N1 `nu_weight_bound` (§5.3: "In the second factor, the range |τ'−τ_k| ≤ 2T has |τ'| ≤ 4T and
  contributes at most 2Ψ₀B; on |τ'−τ_k| =: r > 2T we have |τ'| ≤ 2r, |ν_X(τ')| ≤ B + log(r/T) and
  ψ(r) ≤ c_ϱ r⁻², contributing ≪ B/T. So the second factor is ≤ 3Ψ₀B uniformly in k."):
      ∫_ℝ ψ(τ−a) |ν_X(τ)| dτ ≤ (2Ψ + 5c_ϱ)·B   for a ∈ I = [T,2T],  Ψ := 4 + 2 log(c_ϱL/4w) ≥ Ψ₀.
  Route (constants only differ): |ν_X(τ)| ≤ B + log⁺(|τ|/4T) ≤ B + 2√(|τ|/4T) ≤ B + 2 + 2√(|τ−a|/4T)
  for |a| ≤ 2T, so the integral is ≤ (B+2)∫ψ + T^{-1/2}∫ψ(r)√|r| dr ≤ (B+2)·2Ψ + 2L + 4c_ϱ/w.
* N2 `nu_grid_bound` (§5.3: "The sum over k of the first factor equals ∫_{τ∉I}|ν_X(τ)|σ(τ)dτ with
  σ(τ) := Σ_{k<d} ψ(τ−τ_k) … Hence ∫_{τ∉I}|ν_X|σ ≪ BLl"):
      ∫_{ℝ∖I} |ν_X(τ)| σ(τ) dτ ≤ CN2(c_ϱ)·B·L·l.
Here ψ = `psiA cϱ p` [eq:psidef], B = `B` = l + 4√X and `NuBound p` = [eq:Bdef]
(discharged by nuX_abs_le), all from Zeta23/PrimeSideA/EndsCore.lean.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Real Set

namespace Zeta23
namespace PrimeSide

variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}



lemma CN2_def (cϱ : ℝ) : CN2 cϱ = 100 * (1 + |Real.log cϱ| + |cϱ|) := rfl






/-! ### N2: reduction to the half-line and the majorant -/





















/-! ### N2: integrating the majorant -/













end PrimeSide
end Zeta23
end
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Real Set
open Zeta23
open PrimeSide
variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}

theorem solution (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F) (hν : NuBound p B ν)
    (hBl : p.l ≤ B) (hL2l : p.L ≤ 2 * p.l)
    (hT : 2 * π * Real.exp 8 ≤ p.T) :
    ∫ τ in (p.I)ᶜ, (∑ k ∈ Finset.range p.d, psiA cϱ p (τ - p.tau k)) * |ν τ|
      ≤ CN2 cϱ * (B * (p.L * p.l)) := by
  have hl8 : 8 ≤ p.l := Setting.le_l_of_T hT
  have hL8 : 8 ≤ p.L := hF.eight_le_L
  have hL := hF.L_pos
  have hc4 := hF.four_le_cϱ
  have hc : (0:ℝ) ≤ cϱ := by linarith
  have hB : 0 ≤ B := by linarith
  have hLl : p.L ≤ 2 * p.l := hL2l
  have hpoly : 2 * (B * (2 + 2 * p.L + 25 / 2 * cϱ * p.L + cϱ * p.L ^ 2 / 2 + cϱ * p.L * p.l)
        + p.L * cϱ * B) ≤ 100 * (1 + cϱ) * (B * (p.L * p.l)) := by
    have hLl64 : 64 ≤ p.L * p.l := by
      have := mul_le_mul hL8 hl8 (by norm_num) hL.le; linarith
    have hL2 : p.L ^ 2 ≤ 2 * (p.L * p.l) := by
      rw [sq]; nlinarith [mul_le_mul_of_nonneg_left hLl hL.le]
    -- divide out B ≥ 0
    set M := p.L * p.l with hM
    have hcM : 0 ≤ cϱ * M := by positivity
    have e1 : (4:ℝ) ≤ M := by linarith
    have e2 : 4 * p.L ≤ M := by
      rw [hM]; nlinarith [mul_nonneg hL.le (by linarith : (0:ℝ) ≤ p.l - 4)]
    have e3 : 27 * cϱ * p.L ≤ 4 * (cϱ * M) := by
      have h27 : 27 * p.L ≤ 4 * M := by
        rw [hM]; nlinarith [mul_nonneg hL.le (by linarith : (0:ℝ) ≤ 4 * p.l - 27)]
      have := mul_le_mul_of_nonneg_left h27 hc
      linarith
    have e4 : cϱ * p.L ^ 2 ≤ cϱ * (2 * M) := mul_le_mul_of_nonneg_left hL2 hc
    have inner : 2 * (2 + 2 * p.L + 25 / 2 * cϱ * p.L + cϱ * p.L ^ 2 / 2 + cϱ * p.L * p.l)
        + 2 * (p.L * cϱ) ≤ 100 * (1 + cϱ) * M := by
      have : cϱ * p.L * p.l = cϱ * M := by rw [hM]; ring
      rw [this]
      have hM0 : 0 ≤ M := by linarith
      linarith [e1, e2, e3, e4, hcM, hM0]
    have := mul_le_mul_of_nonneg_left inner hB
    have eB : 2 * (B * (2 + 2 * p.L + 25 / 2 * cϱ * p.L + cϱ * p.L ^ 2 / 2 + cϱ * p.L * p.l)
        + p.L * cϱ * B)
        = B * (2 * (2 + 2 * p.L + 25 / 2 * cϱ * p.L + cϱ * p.L ^ 2 / 2 + cϱ * p.L * p.l)
          + 2 * (p.L * cϱ)) := by ring
    have eR : 100 * (1 + cϱ) * (B * (p.L * p.l)) = B * (100 * (1 + cϱ) * M) := by
      rw [hM]; ring
    rw [eB, eR]
    exact this
  have hCN2 : 100 * (1 + cϱ) ≤ CN2 cϱ := by
    rw [CN2_def, abs_of_nonneg hc]
    have := abs_nonneg (Real.log cϱ)
    nlinarith
  calc ∫ τ in (p.I)ᶜ, (∑ k ∈ Finset.range p.d, psiA cϱ p (τ - p.tau k)) * |ν τ|
      ≤ 2 * (B * (2 + 2 * p.L + 25 / 2 * cϱ * p.L + cϱ * p.L ^ 2 / 2 + cϱ * p.L * p.l)
          + p.L * cϱ * B) := nu_grid_bound_raw hνc hF hν (by linarith) hT
    _ ≤ 100 * (1 + cϱ) * (B * (p.L * p.l)) := hpoly
    _ ≤ CN2 cϱ * (B * (p.L * p.l)) :=
        mul_le_mul_of_nonneg_right hCN2 (by positivity)
