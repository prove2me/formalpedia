-- Prove2me | solution 1 for Zeta23.PrimeSide.calE2_maj_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T03:32:59.252544+00:00
-- url     : https://prove2.me/submissions/992f1c23-190a-4559-9a75-47ba6cc43b4a

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
import Definitions.Def_Zeta23_PrimeSideA_EndsE2
import Definitions.Def_Zeta23_PrimeSideA_EndsNu
import Theorems.Thm_Zeta23_PrimeSide_nu_grid_bound
import Theorems.Thm_Zeta23_PrimeSide_nu_weight_bound_of_L_le_two_B
import Theorems.Thm_Zeta23_PrimeSide_setIntegral_compl_sqI_majK2_le

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
section
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


lemma CN2_nonneg (cϱ : ℝ) : 0 ≤ CN2 cϱ := by
  unfold CN2
  have h1 : 0 ≤ |Real.log cϱ| := abs_nonneg _
  have h2 : 0 ≤ |cϱ| := abs_nonneg _
  linarith




/-- **N1** (§5.3, "the second factor is ≤ 3Ψ₀B uniformly in k"): for a ∈ [T,2T],
  ∫_ℝ ψ(τ−a)|ν_X(τ)| dτ ≤ (2(4 + 2 log(c_ϱL/4w)) + 7c_ϱ)·B   (paper regime B ≥ l, L ≤ 2l). -/
theorem nu_weight_bound (hνc : Continuous ν) (hF : LocalHypsCoreW cϱ p F) (hν : NuBound p B ν)
    (hBl : p.l ≤ B) (hL2l : p.L ≤ 2 * p.l)
    (hT : 1 ≤ p.T) {a : ℝ} (ha : a ∈ Icc p.T (2 * p.T)) :
    ∫ τ : ℝ, psiA cϱ p (τ - a) * |ν τ|
      ≤ (2 * (4 + 2 * Real.log (cϱ * p.L / (4 * p.w))) + 7 * cϱ) * B := by
  have hl4 : 4 ≤ p.l := by linarith [hF.eight_le_L]
  exact nu_weight_bound_of_L_le_two_B hνc hF hν (by linarith) (by linarith) hT ha



/-! ### N2: reduction to the half-line and the majorant -/





















/-! ### N2: integrating the majorant -/













end PrimeSide
end Zeta23
end
end

-- from Zeta23.PrimeSideA.EndsE2
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — [lem:ends], bound for 𝓔₂ (§5.3).  Statement consumed by
Zeta23/PrimeSideA/Ends.lean.
Substrate: Zeta23/PrimeSideA/EndsWeighted.lean; 1-D estimates N1/N2 from
Zeta23/PrimeSideA/EndsNu.lean.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Real Set

namespace Zeta23
namespace PrimeSide

section Assembly

variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}







end Assembly

section Bounds
variable (cϱ lam : ℝ)






end Bounds

end PrimeSide
end Zeta23
end
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Real Set
open Zeta23
open PrimeSide
variable (cϱ lam : ℝ)

theorem solution :
    ∃ C T₀ : ℝ, ∀ (p : Setting) (F : LocalFun) (B : ℝ) (ν : ℝ → ℝ), p.lam = lam → T₀ ≤ p.T →
      LocalHypsCoreW cϱ p F → p.L ≤ 2 * p.l → Continuous ν → NuBound p B ν → p.l ≤ B →
      ∫ q in (sqI p)ᶜ, majK2 cϱ p ν q ≤ C * (p.L ^ 3 * B ^ 2 * p.l * Real.log p.l) := by
  refine ⟨2 * (12 + 4 * max 0 (Real.log cϱ) + 4 * cϱ) * CN2 cϱ,
    2 * π * Real.exp 8, fun p F B ν _ hT hF hL2l hνc hν hBl => ?_⟩
  -- regime
  have hπ3 := Real.pi_gt_three
  have he8 : (1 : ℝ) ≤ Real.exp 8 := Real.one_le_exp (by norm_num)
  have hT8 : 2 * π * Real.exp 8 ≤ p.T := hT
  have hT1 : (1 : ℝ) ≤ p.T := by nlinarith
  have hT0 : (0 : ℝ) < p.T := by linarith
  have hT2π : 2 * π ≤ p.T := by nlinarith
  have hl8 : (8 : ℝ) ≤ p.l := Setting.le_l_of_T hT8
  have hl1 : (1 : ℝ) ≤ p.l := by linarith
  have hlogl2 : (2 : ℝ) ≤ Real.log p.l := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have h1 := Real.exp_one_lt_d9
    calc Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      _ ≤ 2.7182818286 * 2.7182818286 := by nlinarith [Real.exp_pos 1]
      _ ≤ 8 := by norm_num
      _ ≤ p.l := hl8
  have hL8 : (8 : ℝ) ≤ p.L := hF.eight_le_L
  have hL0 : (0 : ℝ) < p.L := by linarith
  have hLl : p.L ≤ 2 * p.l := hL2l
  have hlog2 : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
  have hlogL : Real.log p.L ≤ Real.log p.l + 1 := by
    calc Real.log p.L ≤ Real.log (2 * p.l) := Real.log_le_log hL0 hLl
      _ = Real.log 2 + Real.log p.l := Real.log_mul (by norm_num) (by linarith)
      _ ≤ Real.log p.l + 1 := by linarith
  have hB1 : (1 : ℝ) ≤ B := le_trans hl1 hBl
  have hB0 : (0 : ℝ) ≤ B := by linarith
  have hw1 : (1 : ℝ) ≤ p.w := hF.one_le_w
  have hc4 : (4 : ℝ) ≤ cϱ := hF.four_le_cϱ
  have hm0 : (0 : ℝ) ≤ max 0 (Real.log cϱ) := le_max_left _ _
  have hlogl0 : (0 : ℝ) < Real.log p.l := by linarith
  -- fold the N1 constant into log l
  have hlogbound : Real.log (cϱ * p.L / (4 * p.w)) ≤ max 0 (Real.log cϱ) + Real.log p.l + 1 := by
    calc Real.log (cϱ * p.L / (4 * p.w)) ≤ Real.log (cϱ * p.L) := by
          apply Real.log_le_log (by positivity)
          apply div_le_self (by positivity)
          linarith
      _ = Real.log cϱ + Real.log p.L := Real.log_mul (by positivity) (by positivity)
      _ ≤ max 0 (Real.log cϱ) + Real.log p.l + 1 := by
          have := le_max_right (0 : ℝ) (Real.log cϱ)
          linarith
  set M1 : ℝ := (2 * (4 + 2 * Real.log (cϱ * p.L / (4 * p.w))) + 7 * cϱ) * B with hM1
  have hM1nn : 0 ≤ M1 := by
    rw [hM1]
    have hwle := hF.w_le
    have hlog4w : (0:ℝ) ≤ Real.log (cϱ * p.L / (4 * p.w)) := by
      apply Real.log_nonneg
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    positivity
  have hM1fold : M1 ≤ ((12 + 4 * max 0 (Real.log cϱ) + 4 * cϱ) * Real.log p.l) * B := by
    rw [hM1]
    have key : 2 * (4 + 2 * Real.log (cϱ * p.L / (4 * p.w))) + 7 * cϱ
        ≤ (12 + 4 * max 0 (Real.log cϱ) + 4 * cϱ) * Real.log p.l := by
      have h1 : Real.log (cϱ * p.L / (4 * p.w)) ≤ max 0 (Real.log cϱ) + Real.log p.l + 1 := hlogbound
      nlinarith [mul_nonneg hm0 (by linarith : (0:ℝ) ≤ Real.log p.l - 2),
        mul_nonneg (by linarith : (0:ℝ) ≤ cϱ) (by linarith : (0:ℝ) ≤ Real.log p.l - 2)]
    exact mul_le_mul_of_nonneg_right key hB0
  -- the 1-D estimates
  have hN1 : ∀ a ∈ Icc p.T (2 * p.T),
      ∫ τ : ℝ, psiA cϱ p (τ - a) * |ν τ| ≤ M1 :=
    fun a ha => nu_weight_bound hνc hF hν hBl hL2l hT1 ha
  have hN2 := nu_grid_bound hνc hF hν hBl hL2l hT8
  have htotal := setIntegral_compl_sqI_majK2_le hνc hF hν hB1 hT1 hM1nn hN1 hN2
  refine htotal.trans ?_
  have hc60 : (0:ℝ) ≤ CN2 cϱ := CN2_nonneg cϱ
  have hstep : M1 * (CN2 cϱ * (B * (p.L * p.l)))
      ≤ (((12 + 4 * max 0 (Real.log cϱ) + 4 * cϱ) * Real.log p.l) * B)
        * (CN2 cϱ * (B * (p.L * p.l))) := by
    exact mul_le_mul_of_nonneg_right hM1fold (mul_nonneg hc60 (by positivity))
  calc 2 * (p.L ^ 2 * M1 * (CN2 cϱ * (B * (p.L * p.l))))
      = 2 * p.L ^ 2 * (M1 * (CN2 cϱ * (B * (p.L * p.l)))) := by
        ring
    _ ≤ 2 * p.L ^ 2 * ((((12 + 4 * max 0 (Real.log cϱ) + 4 * cϱ) * Real.log p.l) * B)
        * (CN2 cϱ * (B * (p.L * p.l)))) := by
        refine mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = 2 * (12 + 4 * max 0 (Real.log cϱ) + 4 * cϱ) * CN2 cϱ
        * (p.L ^ 3 * B ^ 2 * p.l * Real.log p.l) := by
        ring
