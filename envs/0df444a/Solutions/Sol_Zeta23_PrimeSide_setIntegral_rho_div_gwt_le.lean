-- Prove2me | solution 1 for Zeta23.PrimeSide.setIntegral_rho_div_gwt_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T05:17:38.22331+00:00
-- url     : https://prove2.me/submissions/9809ea58-7f9e-4698-bfbb-b024bd5b7595

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
import Theorems.Thm_Zeta23_LeafIntegrals_W3_core
import Theorems.Thm_Zeta23_PrimeSide_W1b
import Theorems.Thm_Zeta23_PrimeSide_W1c
import Theorems.Thm_Zeta23_PrimeSide_W1d
import Theorems.Thm_Zeta23_PrimeSide_rho_le_majorant

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



















lemma Setting.d_eq_floor (p : Setting) (hL : 0 < p.L) : p.d = ⌊p.T / p.h⌋₊ := by
  simp only [Setting.d, Setting.h]
  congr 1
  field_simp



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







/-! ### Integrability ("the interchange being justified by absolute convergence", §5.3) -/


















end Structure

section PsiToolkit
/-! ## ψ toolkit  (generic facts about `psiA cϱ p` = min(L, 2/|r|, c/(w r²)) [eq:psidef]).
Statements are consumed by EndsE1/EndsE2. -/
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

theorem psiA_of_ne_zero {r : ℝ} (hr : r ≠ 0) :
    psiA cϱ p r = min p.L (min (2 / |r|) (cϱ / (p.w * r ^ 2))) := by
  simp [psiA, hr]


theorem psiA_le_L (r : ℝ) : psiA cϱ p r ≤ p.L := by
  by_cases hr : r = 0
  · simp [psiA, hr]
  · rw [psiA_of_ne_zero hr]; exact min_le_left _ _

theorem psiA_le_div_sq {r : ℝ} (hr : r ≠ 0) : psiA cϱ p r ≤ cϱ / (p.w * r ^ 2) := by
  rw [psiA_of_ne_zero hr]; exact le_trans (min_le_right _ _) (min_le_right _ _)


theorem psiA_even (r : ℝ) : psiA cϱ p (-r) = psiA cϱ p r := by
  simp [psiA]

theorem psiA_nonneg (hL : 0 ≤ p.L) (hc : 0 ≤ cϱ) (hw : 0 < p.w) (r : ℝ) : 0 ≤ psiA cϱ p r := by
  by_cases hr : r = 0
  · simp [psiA, hr, hL]
  · rw [psiA_of_ne_zero hr]
    refine le_min hL (le_min (by positivity) (by positivity))


theorem psiA_abs (r : ℝ) : psiA cϱ p |r| = psiA cϱ p r := by
  rcases le_or_gt 0 r with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, psiA_even]



theorem psiA_nonneg_of (hF : LocalHypsCoreW cϱ p F) (r : ℝ) : 0 ≤ psiA cϱ p r :=
  psiA_nonneg hF.L_pos.le (by linarith [hF.four_le_cϱ]) (by linarith [hF.one_le_w]) r








/-- ∫_{(Δ,∞)} ψ² ≤ ∫_ℝ ψ² ≤ 8L. -/
theorem setIntegral_psiA_sq_Ioi_le (hF : LocalHypsCoreW cϱ p F) (Δ : ℝ) :
    ∫ r in Set.Ioi Δ, psiA cϱ p r ^ 2 ≤ 8 * p.L :=
  le_trans (setIntegral_le_integral hF.psi_sq_integrable
    (Filter.Eventually.of_forall fun _ => sq_nonneg _)) hF.integral_psi_sq_le



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



theorem W1a (hF : LocalHypsCoreW cϱ p F) :
    ∫ u in (0:ℝ)..1, psiA cϱ p u ^ 2 * (1 + u) ^ 2 ≤ 4 * p.L ^ 2 := by
  have hψ0 := psiA_nonneg_of hF
  have hfi : IntervalIntegrable (fun u => psiA cϱ p u ^ 2 * (1 + u) ^ 2) volume 0 1 :=
    hF.psi_sq_integrable.intervalIntegrable.mul_continuousOn (by fun_prop)
  calc ∫ u in (0:ℝ)..1, psiA cϱ p u ^ 2 * (1 + u) ^ 2
      ≤ ∫ u in (0:ℝ)..1, 4 * p.L ^ 2 := by
        refine intervalIntegral.integral_mono_on zero_le_one hfi intervalIntegrable_const ?_
        intro u hu
        have h1 : psiA cϱ p u ^ 2 ≤ p.L ^ 2 := pow_le_pow_left₀ (hψ0 u) (psiA_le_L u) 2
        have h2 : (1 + u) ^ 2 ≤ 4 := by nlinarith [hu.1, hu.2]
        calc psiA cϱ p u ^ 2 * (1 + u) ^ 2 ≤ p.L ^ 2 * 4 :=
              mul_le_mul h1 h2 (sq_nonneg _) (sq_nonneg _)
          _ = 4 * p.L ^ 2 := by ring
    _ = 4 * p.L ^ 2 := by simp






/-- (W3) the stray term: `∫_ℝ ψ(r)²(2+|r|)² dr ≤ 18L² + 18(c/w)²`, with integrability. -/
theorem W3 (hF : LocalHypsCoreW cϱ p F) :
    Integrable (fun r => psiA cϱ p r ^ 2 * (2 + |r|) ^ 2) ∧
    ∫ r, psiA cϱ p r ^ 2 * (2 + |r|) ^ 2 ≤ 18 * p.L ^ 2 + 18 * (cϱ / p.w) ^ 2 :=
  
  Zeta23.LeafIntegrals.W3_core (psiA cϱ p) p.L cϱ p.w (by linarith [hF.one_le_w]) psiA_abs
    (psiA_nonneg_of hF) psiA_le_L (fun r hr => psiA_le_div_sq hr) hF.psi_sq_integrable

/-! ### Pointwise facts on I -/

theorem distB_nonneg {τ : ℝ} (hτ : τ ∈ Icc p.T (2 * p.T)) : 0 ≤ distB p τ := by
  unfold distB; rcases hτ with ⟨h1, h2⟩; exact le_min (by linarith) (by linarith)

theorem gwt_pos {τ : ℝ} (hτ : τ ∈ Icc p.T (2 * p.T)) : 0 < gwt p τ := by
  unfold gwt; have := distB_nonneg hτ; positivity






/-! ### The majorant for ρ on I -/

/-- `τ_d = T + d h > 2T − h` (since `d = ⌊T/h⌋`). -/
theorem tau_d_gt (hL : 0 < p.L) (_hT : 0 < p.T) : 2 * p.T - p.h < p.tau p.d := by
  have hh : 0 < p.h := by unfold Setting.h; positivity
  have hd : p.d = ⌊p.T / p.h⌋₊ := Setting.d_eq_floor p hL
  have hlt : p.T / p.h < (p.d : ℝ) + 1 := by rw [hd]; exact Nat.lt_floor_add_one _
  have : p.T < ((p.d : ℝ) + 1) * p.h := by rwa [div_lt_iff₀ hh] at hlt
  rw [Setting.tau]
  push_cast
  nlinarith


/-- `h ≤ 1` (as `L ≥ 8 > 2π`). -/
theorem h_le_one (hF : LocalHypsCoreW cϱ p F) : p.h ≤ 1 := by
  have hL := hF.eight_le_L
  unfold Setting.h
  rw [div_le_one (by linarith)]
  linarith [Real.pi_lt_four]

theorem h_pos (hF : LocalHypsCoreW cϱ p F) : 0 < p.h := by
  unfold Setting.h; have := hF.L_pos; positivity


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

theorem solution (hF : LocalHypsCoreW cϱ p F) (_hν : NuBound p B ν) (hT : 1 ≤ p.T) :
    ∫ τ in Icc p.T (2 * p.T), rho p F τ / gwt p τ
      ≤ 2 * (4 * p.L ^ 2 + 4 * (cϱ / p.w) ^ 2
            + (p.h)⁻¹ * (32 * p.L + 4 / 3 * (cϱ / p.w) ^ 2 * Real.log p.T))
        + (18 * p.L ^ 2 + 18 * (cϱ / p.w) ^ 2) := by
  have hT0 : 0 < p.T := by linarith
  have hL := hF.L_pos
  have hh := h_pos hF
  have hh1 := h_le_one hF
  have htd := tau_d_gt hL hT0
  have hψ0 := psiA_nonneg_of hF
  -- the tail integral J(u) := ∫_{(u,∞)} ψ²
  have hJ_nonneg : ∀ u : ℝ, 0 ≤ ∫ r in Set.Ioi u, psiA cϱ p r ^ 2 := fun u =>
    setIntegral_nonneg measurableSet_Ioi (fun r _ => sq_nonneg _)
  have hJ_le : ∀ u : ℝ, ∫ r in Set.Ioi u, psiA cϱ p r ^ 2 ≤ 8 * p.L := fun u =>
    setIntegral_psiA_sq_Ioi_le hF u
  have hJ_anti : Antitone (fun u : ℝ => ∫ r in Set.Ioi u, psiA cϱ p r ^ 2) := by
    intro u v huv
    exact setIntegral_mono_set hF.psi_sq_integrable.integrableOn
      (ae_of_all _ fun r => sq_nonneg _) (Set.Ioi_subset_Ioi huv).eventuallyLE
  have hJ_meas : Measurable (fun u : ℝ => ∫ r in Set.Ioi u, psiA cϱ p r ^ 2) :=
    hJ_anti.measurable
  have hW_nonneg : ∀ u, 0 ≤ Wfun cϱ p u := fun u =>
    add_nonneg (sq_nonneg _) (mul_nonneg (inv_nonneg.mpr hh.le) (hJ_nonneg u))
  -- local integrability of J, of the W-majorant Φ(u) := W(u)(1+u)², and of its two pieces
  have hJon : ∀ s : Set ℝ, volume s ≠ ⊤ → ∀ (e : ℝ → ℝ), Measurable e →
      IntegrableOn (fun u => ∫ r in Set.Ioi (e u), psiA cϱ p r ^ 2) s := by
    intro s hs e he
    refine Integrable.mono' (g := fun _ => 8 * p.L) (integrableOn_const hs)
      ((hJ_meas.comp he).aestronglyMeasurable) (ae_of_all _ fun u => ?_)
    rw [Real.norm_of_nonneg (hJ_nonneg _)]
    exact hJ_le _
  have hvol : ∀ a b : ℝ, volume (Icc a b) ≠ ⊤ := fun a b => by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hΦon : ∀ a b : ℝ, IntegrableOn (fun u => Wfun cϱ p u * (1 + u) ^ 2) (Icc a b) := by
    intro a b
    have h1 : IntegrableOn (fun u => Wfun cϱ p u) (Icc a b) := by
      simp only [Wfun]
      exact hF.psi_sq_integrable.integrableOn.add
        ((hJon _ (hvol a b) id measurable_id).const_mul _)
    exact h1.mul_continuousOn (by fun_prop : Continuous fun u : ℝ => (1 + u) ^ 2).continuousOn
      isCompact_Icc
  have hP1on : ∀ a b : ℝ, IntegrableOn (fun u => psiA cϱ p u ^ 2 * (1 + u) ^ 2) (Icc a b) :=
    fun a b => hF.psi_sq_integrable.integrableOn.mul_continuousOn
      (by fun_prop : Continuous fun u : ℝ => (1 + u) ^ 2).continuousOn isCompact_Icc
  have hP2on : ∀ a b : ℝ, IntegrableOn
      (fun u => (∫ r in Set.Ioi u, psiA cϱ p r ^ 2) * (1 + u) ^ 2) (Icc a b) :=
    fun a b => (hJon _ (hvol a b) id measurable_id).mul_continuousOn
      (by fun_prop : Continuous fun u : ℝ => (1 + u) ^ 2).continuousOn isCompact_Icc
  have hii : ∀ {f : ℝ → ℝ} {a b : ℝ}, a ≤ b → IntegrableOn f (Icc a b) →
      IntervalIntegrable f volume a b := by
    intro f a b hab h
    exact (h.mono_set (by rw [Set.uIcc_of_le hab])).intervalIntegrable
  -- STEP 1: pointwise majorant on I
  have hpt : ∀ τ ∈ Icc p.T (2 * p.T), rho p F τ / gwt p τ
      ≤ Wfun cϱ p (τ - p.T) * (1 + (τ - p.T)) ^ 2
        + Wfun cϱ p (2 * p.T - τ) * (1 + (2 * p.T - τ)) ^ 2
        + psiA cϱ p (p.tau p.d - τ) ^ 2 * (2 + |p.tau p.d - τ|) ^ 2 := by
    intro τ hτ
    have hm0 := distB_nonneg hτ
    have hmaj := rho_le_majorant hF hT0 hτ
    have e : rho p F τ / gwt p τ = rho p F τ * (1 + distB p τ) ^ 2 := by
      unfold gwt; rw [div_inv_eq_mul]
    rw [e]
    have hmL : distB p τ ≤ τ - p.T := min_le_left _ _
    have hmR : distB p τ ≤ 2 * p.T - τ := min_le_right _ _
    have hmS : 1 + distB p τ ≤ 2 + |p.tau p.d - τ| := by
      have := le_abs_self (p.tau p.d - τ); linarith
    have hW1 := hW_nonneg (τ - p.T)
    have hW2 := hW_nonneg (2 * p.T - τ)
    have hsqL : (1 + distB p τ) ^ 2 ≤ (1 + (τ - p.T)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hsqR : (1 + distB p τ) ^ 2 ≤ (1 + (2 * p.T - τ)) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have hsqS : (1 + distB p τ) ^ 2 ≤ (2 + |p.tau p.d - τ|) ^ 2 :=
      pow_le_pow_left₀ (by linarith) hmS 2
    calc rho p F τ * (1 + distB p τ) ^ 2
        ≤ (Wfun cϱ p (τ - p.T) + Wfun cϱ p (2 * p.T - τ) + psiA cϱ p (p.tau p.d - τ) ^ 2)
            * (1 + distB p τ) ^ 2 := mul_le_mul_of_nonneg_right hmaj (sq_nonneg _)
      _ = Wfun cϱ p (τ - p.T) * (1 + distB p τ) ^ 2
          + Wfun cϱ p (2 * p.T - τ) * (1 + distB p τ) ^ 2
          + psiA cϱ p (p.tau p.d - τ) ^ 2 * (1 + distB p τ) ^ 2 := by ring
      _ ≤ _ := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hsqL hW1)
            (mul_le_mul_of_nonneg_left hsqR hW2))
            (mul_le_mul_of_nonneg_left hsqS (sq_nonneg _))
  -- STEP 2: integrability of the three majorant pieces on I
  set I : Set ℝ := Icc p.T (2 * p.T) with hIdef
  have hIvol : volume I ≠ ⊤ := hvol _ _
  have hA : IntegrableOn (fun τ => Wfun cϱ p (τ - p.T) * (1 + (τ - p.T)) ^ 2) I := by
    have h1 : IntegrableOn (fun τ => Wfun cϱ p (τ - p.T)) I := by
      simp only [Wfun]
      exact (hF.psi_sq_integrable.comp_sub_right p.T).integrableOn.add
        ((hJon _ hIvol (fun τ => τ - p.T) (measurable_id.sub_const _)).const_mul _)
    exact h1.mul_continuousOn
      (by fun_prop : Continuous fun τ : ℝ => (1 + (τ - p.T)) ^ 2).continuousOn isCompact_Icc
  have hB : IntegrableOn (fun τ => Wfun cϱ p (2 * p.T - τ) * (1 + (2 * p.T - τ)) ^ 2) I := by
    have h1 : IntegrableOn (fun τ => Wfun cϱ p (2 * p.T - τ)) I := by
      simp only [Wfun]
      exact (hF.psi_sq_integrable.comp_sub_left (2 * p.T)).integrableOn.add
        ((hJon _ hIvol (fun τ => 2 * p.T - τ) (measurable_const.sub measurable_id)).const_mul _)
    exact h1.mul_continuousOn
      (by fun_prop : Continuous fun τ : ℝ => (1 + (2 * p.T - τ)) ^ 2).continuousOn
      isCompact_Icc
  have hC : IntegrableOn
      (fun τ => psiA cϱ p (p.tau p.d - τ) ^ 2 * (2 + |p.tau p.d - τ|) ^ 2) I :=
    ((W3 hF).1.comp_sub_left (p.tau p.d)).integrableOn
  -- STEP 3: integrate the pointwise bound
  have hmono : ∫ τ in I, rho p F τ / gwt p τ
      ≤ ∫ τ in I, (Wfun cϱ p (τ - p.T) * (1 + (τ - p.T)) ^ 2
        + Wfun cϱ p (2 * p.T - τ) * (1 + (2 * p.T - τ)) ^ 2
        + psiA cϱ p (p.tau p.d - τ) ^ 2 * (2 + |p.tau p.d - τ|) ^ 2) := by
    refine integral_mono_of_nonneg ?_ ((hA.add hB).add hC) ?_
    · exact ae_restrict_of_forall_mem measurableSet_Icc fun τ hτ =>
        div_nonneg (rho_nonneg hF τ) (gwt_pos hτ).le
    · exact ae_restrict_of_forall_mem measurableSet_Icc hpt
  -- STEP 4: the three integrals
  -- (C) the stray term
  have hCval : ∫ τ in I, psiA cϱ p (p.tau p.d - τ) ^ 2 * (2 + |p.tau p.d - τ|) ^ 2
      ≤ 18 * p.L ^ 2 + 18 * (cϱ / p.w) ^ 2 := by
    calc ∫ τ in I, psiA cϱ p (p.tau p.d - τ) ^ 2 * (2 + |p.tau p.d - τ|) ^ 2
        ≤ ∫ τ, psiA cϱ p (p.tau p.d - τ) ^ 2 * (2 + |p.tau p.d - τ|) ^ 2 :=
          setIntegral_le_integral ((W3 hF).1.comp_sub_left (p.tau p.d))
            (ae_of_all _ fun τ => by positivity)
      _ = ∫ r, psiA cϱ p r ^ 2 * (2 + |r|) ^ 2 :=
          integral_sub_left_eq_self (fun r => psiA cϱ p r ^ 2 * (2 + |r|) ^ 2) volume (p.tau p.d)
      _ ≤ _ := (W3 hF).2
  -- (A),(B): change of variables to ∫_0^T W(u)(1+u)²
  have hT2 : p.T ≤ 2 * p.T := by linarith
  have hAval : ∫ τ in I, Wfun cϱ p (τ - p.T) * (1 + (τ - p.T)) ^ 2
      = ∫ u in (0:ℝ)..p.T, Wfun cϱ p u * (1 + u) ^ 2 := by
    rw [hIdef, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT2,
      intervalIntegral.integral_comp_sub_right (fun u => Wfun cϱ p u * (1 + u) ^ 2) p.T,
      sub_self, show 2 * p.T - p.T = p.T by ring]
  have hBval : ∫ τ in I, Wfun cϱ p (2 * p.T - τ) * (1 + (2 * p.T - τ)) ^ 2
      = ∫ u in (0:ℝ)..p.T, Wfun cϱ p u * (1 + u) ^ 2 := by
    rw [hIdef, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT2,
      intervalIntegral.integral_comp_sub_left (fun u => Wfun cϱ p u * (1 + u) ^ 2) (2 * p.T),
      sub_self, show 2 * p.T - p.T = p.T by ring]
  -- the main 1-D integral: split at 1 and expand W = ψ² + h⁻¹ J
  have hΦ01 := hii zero_le_one (hΦon 0 1)
  have hΦ1T := hii hT (hΦon 1 p.T)
  have hexpand : ∀ {a b : ℝ}, a ≤ b →
      ∫ u in a..b, Wfun cϱ p u * (1 + u) ^ 2
        = (∫ u in a..b, psiA cϱ p u ^ 2 * (1 + u) ^ 2)
          + (p.h)⁻¹ * ∫ u in a..b, (∫ r in Set.Ioi u, psiA cϱ p r ^ 2) * (1 + u) ^ 2 := by
    intro a b hab
    have e : (fun u => Wfun cϱ p u * (1 + u) ^ 2)
        = fun u => psiA cϱ p u ^ 2 * (1 + u) ^ 2
          + (p.h)⁻¹ * ((∫ r in Set.Ioi u, psiA cϱ p r ^ 2) * (1 + u) ^ 2) := by
      funext u; simp only [Wfun]; ring
    rw [e, intervalIntegral.integral_add (hii hab (hP1on a b))
      ((hii hab (hP2on a b)).const_mul _), intervalIntegral.integral_const_mul]
  have hmain : ∫ u in (0:ℝ)..p.T, Wfun cϱ p u * (1 + u) ^ 2
      ≤ 4 * p.L ^ 2 + 4 * (cϱ / p.w) ^ 2
        + (p.h)⁻¹ * (32 * p.L + 4 / 3 * (cϱ / p.w) ^ 2 * Real.log p.T) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hΦ01 hΦ1T,
      hexpand zero_le_one, hexpand hT]
    have h1 := W1a hF
    have h2 := W1b hF hT
    have h3 := W1c hF
    have h4 := W1d hF hT
    have hhi : 0 ≤ (p.h)⁻¹ := inv_nonneg.mpr hh.le
    nlinarith [mul_le_mul_of_nonneg_left h3 hhi, mul_le_mul_of_nonneg_left h4 hhi]
  -- assemble
  calc ∫ τ in I, rho p F τ / gwt p τ
      ≤ ∫ τ in I, (Wfun cϱ p (τ - p.T) * (1 + (τ - p.T)) ^ 2
          + Wfun cϱ p (2 * p.T - τ) * (1 + (2 * p.T - τ)) ^ 2
          + psiA cϱ p (p.tau p.d - τ) ^ 2 * (2 + |p.tau p.d - τ|) ^ 2) := hmono
    _ = (∫ τ in I, (Wfun cϱ p (τ - p.T) * (1 + (τ - p.T)) ^ 2
          + Wfun cϱ p (2 * p.T - τ) * (1 + (2 * p.T - τ)) ^ 2))
        + ∫ τ in I, psiA cϱ p (p.tau p.d - τ) ^ 2 * (2 + |p.tau p.d - τ|) ^ 2 :=
          integral_add (hA.add hB) hC
    _ = (∫ τ in I, Wfun cϱ p (τ - p.T) * (1 + (τ - p.T)) ^ 2)
        + (∫ τ in I, Wfun cϱ p (2 * p.T - τ) * (1 + (2 * p.T - τ)) ^ 2)
        + ∫ τ in I, psiA cϱ p (p.tau p.d - τ) ^ 2 * (2 + |p.tau p.d - τ|) ^ 2 := by
          rw [integral_add hA hB]
    _ ≤ _ := by rw [hAval, hBval]; linarith [hmain, hCval]
