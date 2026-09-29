-- Prove2me | solution 1 for Zeta23.PrimeSide.calE1_maj_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T05:14:31.810368+00:00
-- url     : https://prove2.me/submissions/89fb6371-f376-421e-85cd-38c41294fdde

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
import Theorems.Thm_Zeta23_LeafIntegrals_Ig_core
import Theorems.Thm_Zeta23_PrimeSide_majK1_le
import Theorems.Thm_Zeta23_PrimeSide_setIntegral_rho_div_gwt_le

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

-- from Zeta23.PrimeSideA.EndsCore
section
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





theorem isCompact_sqI : IsCompact (sqI p) := isCompact_Icc.prod isCompact_Icc

theorem measurableSet_sqI : MeasurableSet (sqI p) := measurableSet_Icc.prod measurableSet_Icc

/-! ### Integrability ("the interchange being justified by absolute convergence", §5.3) -/


















end Structure

section PsiToolkit
/-! ## ψ toolkit  (generic facts about `psiA cϱ p` = min(L, 2/|r|, c/(w r²)) [eq:psidef]).
Statements are consumed by EndsE1/EndsE2. -/
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}























end PsiToolkit

section Kbounds
/-! ## [eq:Kbounds] pointwise (§5.3) -/
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}


lemma sum_Ico_int_eq (p : Setting) (F : LocalFun) (τ : ℝ) :
    ∑ k ∈ Finset.Ico (0:ℤ) (p.d : ℤ), F.phiHat (τ - p.tau k) ^ 2
      = ∑ k : Fin p.d, F.phiHat (τ - p.tau (k : ℕ)) ^ 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => F.phiHat (τ - p.tau (n : ℕ)) ^ 2) p.d]
  rw [show Finset.Ico (0:ℤ) (p.d : ℤ) = (Finset.range p.d).image (fun n : ℕ => (n : ℤ)) by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h0, hd⟩
      exact ⟨k.toNat, by omega, by omega⟩
    · rintro ⟨n, hn, rfl⟩
      omega]
  rw [Finset.sum_image (fun a _ b _ h => by exact_mod_cast h)]

lemma hasSum_total (hF : LocalHypsCoreW cϱ p F) (τ : ℝ) :
    HasSum (fun k : ℤ => F.phiHat (τ - p.tau k) ^ 2) (F.a * p.L ^ 2) := by
  have h := hF.poisson τ τ
  rw [sub_self, hF.Phi_zero] at h
  have h2 : HasSum (fun k : ℤ => F.phiHat (τ - p.tau k) ^ 2) (p.L * (F.a * p.L)) := by
    refine HasSum.congr_fun h fun k => ?_
    rw [sq]
  rwa [show p.L * (F.a * p.L) = F.a * p.L ^ 2 by ring] at h2

/-- Poisson diagonal, finite part: `Σ_{k<d} φ̂(τ−τ_k)² ≤ aL²`, i.e. `ρ(τ) ≥ 0`. -/
theorem rho_nonneg (hF : LocalHypsCoreW cϱ p F) (τ : ℝ) : 0 ≤ rho p F τ := by
  unfold rho
  have htot := hasSum_total hF τ
  have hle : ∑ k ∈ Finset.Ico (0:ℤ) (p.d : ℤ), F.phiHat (τ - p.tau k) ^ 2 ≤ F.a * p.L ^ 2 :=
    sum_le_hasSum _ (fun i _ => sq_nonneg _) htot
  rw [sum_Ico_int_eq] at hle
  linarith





/-! ### K_out pointwise (weighted AM–GM), for 𝓔₁ -/





end Kbounds


end PrimeSide
end Zeta23
end
end

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

/-- (Ig) `∫_I g ≤ 2`. -/
theorem setIntegral_gwt_le (hT : 0 < p.T) : ∫ τ in Icc p.T (2 * p.T), gwt p τ ≤ 2 := by
  
  have := Zeta23.LeafIntegrals.Ig_core p.T hT
  unfold gwt distB
  exact this









/-! ### Pointwise facts on I -/

theorem distB_nonneg {τ : ℝ} (hτ : τ ∈ Icc p.T (2 * p.T)) : 0 ≤ distB p τ := by
  unfold distB; rcases hτ with ⟨h1, h2⟩; exact le_min (by linarith) (by linarith)

theorem gwt_pos {τ : ℝ} (hτ : τ ∈ Icc p.T (2 * p.T)) : 0 < gwt p τ := by
  unfold gwt; have := distB_nonneg hτ; positivity

/-- on I the log⁺ term of [eq:Bdef] vanishes: `|ν(τ)| ≤ B`. -/
theorem abs_nuX_le_B_onI (hν : NuBound p B ν) (hT : 0 < p.T) {τ : ℝ} (hτ : τ ∈ Icc p.T (2 * p.T)) :
    |ν τ| ≤ B := by
  have h := hν τ
  have hτ0 : 0 ≤ τ := by linarith [hτ.1]
  have hmax : max (Real.log (|τ| / (4 * p.T))) 0 = 0 := by
    rw [max_eq_right]
    apply Real.log_nonpos (by positivity)
    rw [div_le_one (by positivity), abs_of_nonneg hτ0]
    linarith [hτ.2]
  rw [hmax, add_zero] at h
  exact h





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
variable (cϱ lam : ℝ)

theorem solution :
    ∃ C T₀ : ℝ, ∀ (p : Setting) (F : LocalFun) (B : ℝ) (ν : ℝ → ℝ), p.lam = lam → T₀ ≤ p.T →
      LocalHypsCoreW cϱ p F → p.L ≤ 2 * p.l → Continuous ν → NuBound p B ν →
      ∫ q in sqI p, majK1 p F ν q ≤ C * (p.L ^ 3 * B ^ 2 * p.l) := by
  refine ⟨4 * (180 + 40 * cϱ ^ 2), (2 * π) ^ 2, fun p F B ν hplam hT hF hL2l hνc hν => ?_⟩
  -- regime
  have hπ := Real.pi_gt_three
  have hT1 : (1:ℝ) ≤ p.T := by nlinarith
  have hT0 : (0:ℝ) < p.T := by linarith
  have hL8 := hF.eight_le_L
  have hL0 := hF.L_pos
  have hc4 := hF.four_le_cϱ
  have hw1 := hF.one_le_w
  have hl1 : (1:ℝ) ≤ p.l := hF.one_le_l
  have hlogT : Real.log p.T ≤ 2 * p.l := by
    -- log T = l + log(2π) and log(2π) ≤ l since T ≥ (2π)²
    have e : Real.log p.T = p.l + Real.log (2 * π) := by
      show Real.log p.T = Real.log (p.T / (2 * π)) + Real.log (2 * π)
      rw [Real.log_div (by linarith) (by positivity)]; ring
    have h2 : Real.log (2 * π) ≤ p.l := by
      show Real.log (2 * π) ≤ Real.log (p.T / (2 * π))
      apply Real.log_le_log (by positivity)
      rw [le_div_iff₀ (by positivity)]; nlinarith
    linarith
  have hB0 : 0 ≤ B := by
    have := abs_nuX_le_B_onI hν hT0 (τ := p.T) ⟨le_rfl, by linarith⟩
    exact le_trans (abs_nonneg _) this
  -- the two 1-D integrals
  have hIg := setIntegral_gwt_le (p := p) hT0
  have hR := setIntegral_rho_div_gwt_le hF hν hT1
  set R := ∫ τ in Icc p.T (2 * p.T), rho p F τ / gwt p τ with hRdef
  set G := ∫ τ in Icc p.T (2 * p.T), gwt p τ with hGdef
  have hG0 : 0 ≤ G := setIntegral_nonneg measurableSet_Icc fun τ hτ => (gwt_pos hτ).le
  have hR0 : 0 ≤ R := setIntegral_nonneg measurableSet_Icc fun τ hτ =>
    div_nonneg (rho_nonneg hF τ) (gwt_pos hτ).le
  -- continuity / integrability on the compact square
  have hρc : Continuous (rho p F) := by
    have := hF.phiHat_cont; unfold rho; fun_prop
  have hdistc : Continuous (distB p) := by unfold distB; fun_prop
  have hgc : ContinuousOn (gwt p) (Icc p.T (2 * p.T)) := by
    unfold gwt
    refine ContinuousOn.inv₀ (by fun_prop) fun τ hτ => ?_
    have := distB_nonneg (p := p) hτ; positivity
  have hρg : ContinuousOn (fun τ => rho p F τ / gwt p τ) (Icc p.T (2 * p.T)) :=
    hρc.continuousOn.div hgc fun τ hτ => (gwt_pos hτ).ne'
  have hfst : ∀ {f : ℝ → ℝ}, ContinuousOn f (Icc p.T (2 * p.T)) →
      ContinuousOn (fun q : ℝ × ℝ => f q.1) (sqI p) := fun hf =>
    hf.comp continuous_fst.continuousOn fun q hq => hq.1
  have hsnd : ∀ {f : ℝ → ℝ}, ContinuousOn f (Icc p.T (2 * p.T)) →
      ContinuousOn (fun q : ℝ × ℝ => f q.2) (sqI p) := fun hf =>
    hf.comp continuous_snd.continuousOn fun q hq => hq.2
  have hM1c : ContinuousOn (fun q : ℝ × ℝ => rho p F q.1 / gwt p q.1 * gwt p q.2) (sqI p) :=
    (hfst hρg).mul (hsnd hgc)
  have hM2c : ContinuousOn (fun q : ℝ × ℝ => gwt p q.1 * (rho p F q.2 / gwt p q.2)) (sqI p) :=
    (hfst hgc).mul (hsnd hρg)
  have hcpt : IsCompact (sqI p) := isCompact_sqI
  have hM1i : IntegrableOn (fun q : ℝ × ℝ => rho p F q.1 / gwt p q.1 * gwt p q.2) (sqI p) :=
    hM1c.integrableOn_compact hcpt
  have hM2i : IntegrableOn (fun q : ℝ × ℝ => gwt p q.1 * (rho p F q.2 / gwt p q.2)) (sqI p) :=
    hM2c.integrableOn_compact hcpt
  have hfi : IntegrableOn (majK1 p F ν) (sqI p) := by
    have hνa : ContinuousOn (fun τ => |ν τ|) (Icc p.T (2 * p.T)) := hνc.abs.continuousOn
    have hc : ContinuousOn (majK1 p F ν) (sqI p) := by
      have := ((hM1c.add hM2c).const_smul (p.L ^ 2)).mul ((hfst hνa).mul (hsnd hνa))
      refine this.congr fun q hq => ?_
      simp only [majK1, Pi.smul_apply, Pi.add_apply, Pi.mul_apply, smul_eq_mul]
    exact hc.integrableOn_compact hcpt
  -- ∫_{sqI} majK1 ≤ L²B²(RG + GR)
  have hmain : ∫ q in sqI p, majK1 p F ν q ≤ p.L ^ 2 * B ^ 2 * (R * G + G * R) := by
    have step2 : ∫ q in sqI p, majK1 p F ν q
        ≤ ∫ q in sqI p, p.L ^ 2 * B ^ 2 *
          (rho p F q.1 / gwt p q.1 * gwt p q.2 + gwt p q.1 * (rho p F q.2 / gwt p q.2)) := by
      refine setIntegral_mono_on hfi ((hM1i.add hM2i).const_mul _) measurableSet_sqI
        fun q hq => majK1_le hF hν hT0 hq
    have step3 : ∫ q in sqI p, p.L ^ 2 * B ^ 2 *
          (rho p F q.1 / gwt p q.1 * gwt p q.2 + gwt p q.1 * (rho p F q.2 / gwt p q.2))
        = p.L ^ 2 * B ^ 2 * (R * G + G * R) := by
      rw [integral_const_mul, integral_add hM1i hM2i]
      congr 1
      unfold sqI
      rw [Measure.volume_eq_prod, setIntegral_prod_mul (fun τ => rho p F τ / gwt p τ) (gwt p),
        setIntegral_prod_mul (gwt p) (fun τ => rho p F τ / gwt p τ)]
      rfl
    linarith
  -- numerics
  have hcw : (cϱ / p.w) ^ 2 ≤ cϱ ^ 2 := by
    have : cϱ / p.w ≤ cϱ := div_le_self (by linarith) hw1
    have : 0 ≤ cϱ / p.w := by positivity
    nlinarith
  have hh : (p.h)⁻¹ = p.L / (2 * π) := by unfold Setting.h; rw [inv_div]
  have hhL : (p.h)⁻¹ ≤ p.L := by
    rw [hh, div_le_iff₀ (by positivity)]; nlinarith
  have hRle : R ≤ (180 + 40 * cϱ ^ 2) * (p.L * p.l) := by
    have hlog0 : 0 ≤ Real.log p.T := Real.log_nonneg hT1
    have h1 : (p.h)⁻¹ * (32 * p.L + 4 / 3 * (cϱ / p.w) ^ 2 * Real.log p.T)
        ≤ p.L * (32 * p.L + 4 / 3 * cϱ ^ 2 * (2 * p.l)) := by
      apply mul_le_mul hhL _ (by positivity) hL0.le
      gcongr
    have hLl2 : p.L ^ 2 ≤ 2 * (p.L * p.l) := by nlinarith
    have hLl1 : 1 ≤ p.L * p.l := by nlinarith
    have hc2 : cϱ ^ 2 ≤ cϱ ^ 2 * (p.L * p.l) := by nlinarith [sq_nonneg cϱ]
    nlinarith
  calc ∫ q in sqI p, majK1 p F ν q ≤ p.L ^ 2 * B ^ 2 * (R * G + G * R) := hmain
    _ = 2 * (p.L ^ 2 * B ^ 2) * (R * G) := by ring
    _ ≤ 2 * (p.L ^ 2 * B ^ 2) * ((180 + 40 * cϱ ^ 2) * (p.L * p.l) * 2) := by
        gcongr
    _ = 4 * (180 + 40 * cϱ ^ 2) * (p.L ^ 3 * B ^ 2 * p.l) := by ring
