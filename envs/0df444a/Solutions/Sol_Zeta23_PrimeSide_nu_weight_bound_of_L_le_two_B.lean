-- Prove2me | solution 1 for Zeta23.PrimeSide.nu_weight_bound_of_L_le_two_B
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T04:49:21.586931+00:00
-- url     : https://prove2.me/submissions/14a39bc6-cd4d-4db2-bf62-49ca4bda28ee

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
import Theorems.Thm_Zeta23_PrimeSide_integrable_psiA_mul_sqrt
import Theorems.Thm_Zeta23_PrimeSide_integrable_psiA_shift_mul_nu
import Theorems.Thm_Zeta23_PrimeSide_integral_psiA_mul_sqrt_le
import Theorems.Thm_Zeta23_PrimeSide_sqrt_shift_le

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







/-! ### Integrability ("the interchange being justified by absolute convergence", §5.3) -/


















end Structure

section PsiToolkit
/-! ## ψ toolkit  (generic facts about `psiA cϱ p` = min(L, 2/|r|, c/(w r²)) [eq:psidef]).
Statements are consumed by EndsE1/EndsE2. -/
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

theorem psiA_of_ne_zero {r : ℝ} (hr : r ≠ 0) :
    psiA cϱ p r = min p.L (min (2 / |r|) (cϱ / (p.w * r ^ 2))) := by
  simp [psiA, hr]





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


/-- ∫_ℝ ψ = 2 ∫_{(0,∞)} ψ (ψ even). -/
theorem integral_psiA_eq_two_mul (_hF : LocalHypsCoreW cϱ p F) :
    ∫ r, psiA cϱ p r = 2 * ∫ r in Set.Ioi 0, psiA cϱ p r := by
  have h := integral_comp_abs (f := psiA cϱ p)
  simp only [psiA_abs] at h
  exact h

theorem psiA_nonneg_of (hF : LocalHypsCoreW cϱ p F) (r : ℝ) : 0 ≤ psiA cϱ p r :=
  psiA_nonneg hF.L_pos.le (by linarith [hF.four_le_cϱ]) (by linarith [hF.one_le_w]) r










/-- `2Ψ₀ := ∫_ℝ ψ ≤ 2(4 + 2 log(c_ϱ L/4w))` [eq:psiints]. -/
theorem integral_psiA_le (hF : LocalHypsCoreW cϱ p F) :
    ∫ r, psiA cϱ p r ≤ 2 * (4 + 2 * Real.log (cϱ * p.L / (4 * p.w))) := by
  rw [integral_psiA_eq_two_mul hF]; linarith [hF.integral_psi_Ioi_le]

end PsiToolkit

section Kbounds
/-! ## [eq:Kbounds] pointwise (§5.3) -/
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}









/-! ### K_out pointwise (weighted AM–GM), for 𝓔₁ -/





end Kbounds


end PrimeSide
end Zeta23
end
end

-- from Zeta23.PrimeSideA.EndsWeighted
section
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

theorem max_log_le_two_sqrt {x : ℝ} (hx : 0 ≤ x) : max (Real.log x) 0 ≤ 2 * Real.sqrt x := by
  refine max_le ?_ (by positivity)
  rcases eq_or_lt_of_le hx with rfl | hx'
  · simp
  · have h := Real.log_le_rpow_div hx (by norm_num : (0 : ℝ) < 1 / 2)
    rw [Real.sqrt_eq_rpow]
    calc Real.log x ≤ x ^ (1 / 2 : ℝ) / (1 / 2) := h
      _ = 2 * x ^ (1 / 2 : ℝ) := by ring



theorem abs_nuX_le_B_add_sqrt (hν : NuBound p B ν) (hT : 0 < p.T) (τ : ℝ) :
    |ν τ| ≤ B + 2 * Real.sqrt (|τ| / (4 * p.T)) := by
  have h := hν τ
  refine h.trans ?_
  gcongr
  exact max_log_le_two_sqrt (by positivity)



end Prelim

section Weighted

variable {cϱ : ℝ} {p : Setting} {F : LocalFun} {ν : ℝ → ℝ} {B : ℝ}

/-- ψ(· − a) is integrable. -/
theorem psiA_shift_integrable (hF : LocalHypsCoreW cϱ p F) (a : ℝ) :
    Integrable (fun τ : ℝ => psiA cϱ p (τ - a)) :=
  hF.psi_integrable.comp_sub_right a

/-- ∫ ψ(τ − a) dτ = ∫ ψ. -/
theorem integral_psiA_shift (a : ℝ) :
    ∫ τ : ℝ, psiA cϱ p (τ - a) = ∫ r : ℝ, psiA cϱ p r :=
  integral_sub_right_eq_self (psiA cϱ p) a



end Weighted

section Grid

variable {cϱ : ℝ} {p : Setting} {F : LocalFun}



end Grid

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
    (hL2B : p.L ≤ 2 * B) (hB4 : 4 ≤ B)
    (hT : 1 ≤ p.T) {a : ℝ} (ha : a ∈ Icc p.T (2 * p.T)) :
    ∫ τ : ℝ, psiA cϱ p (τ - a) * |ν τ|
      ≤ (2 * (4 + 2 * Real.log (cϱ * p.L / (4 * p.w))) + 7 * cϱ) * B := by
  have hT0 : 0 < p.T := by linarith
  have hL := hF.L_pos
  have hw1 := hF.one_le_w
  have hw : 0 < p.w := by linarith
  have hc4 := hF.four_le_cϱ
  have hc : (0 : ℝ) ≤ cϱ := by linarith
  have hB1 : 1 ≤ B := by linarith
  have hB0 : 0 ≤ B := by linarith
  -- pointwise domination (same as in integrable_psiA_shift_mul_nu)
  have hpt : ∀ τ, psiA cϱ p (τ - a) * |ν τ|
      ≤ psiA cϱ p (τ - a) * (B + 2)
        + psiA cϱ p (τ - a) * Real.sqrt |τ - a| / Real.sqrt p.T := by
    intro τ
    have hν1 : |ν τ| ≤ B + 2 * Real.sqrt (|τ| / (4 * p.T)) :=
      abs_nuX_le_B_add_sqrt hν hT0 τ
    have hsh : Real.sqrt (|τ| / (4 * p.T)) ≤ 1 + Real.sqrt (|τ - a| / (4 * p.T)) := by
      have := sqrt_shift_le (a := a) (r := τ - a) (T' := p.T) hT0 (by
        rw [abs_of_nonneg (by linarith [ha.1] : (0:ℝ) ≤ a)]
        linarith [ha.2])
      simpa using this
    have hsq : Real.sqrt (|τ - a| / (4 * p.T)) = Real.sqrt |τ - a| / (2 * Real.sqrt p.T) := by
      rw [Real.sqrt_div (abs_nonneg _), show (4 : ℝ) * p.T = 2 ^ 2 * p.T by norm_num,
        Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
    have hs0 : 0 < Real.sqrt p.T := Real.sqrt_pos.mpr hT0
    have h2 : 2 * Real.sqrt (|τ - a| / (4 * p.T)) = Real.sqrt |τ - a| / Real.sqrt p.T := by
      rw [hsq]; field_simp
    have hbound : |ν τ| ≤ (B + 2) + Real.sqrt |τ - a| / Real.sqrt p.T := by
      calc |ν τ| ≤ B + 2 * Real.sqrt (|τ| / (4 * p.T)) := hν1
        _ ≤ B + 2 * (1 + Real.sqrt (|τ - a| / (4 * p.T))) := by gcongr
        _ = (B + 2) + 2 * Real.sqrt (|τ - a| / (4 * p.T)) := by ring
        _ = (B + 2) + Real.sqrt |τ - a| / Real.sqrt p.T := by rw [h2]
    calc psiA cϱ p (τ - a) * |ν τ|
        ≤ psiA cϱ p (τ - a) * ((B + 2) + Real.sqrt |τ - a| / Real.sqrt p.T) :=
          mul_le_mul_of_nonneg_left hbound (psiA_nonneg_of hF _)
      _ = _ := by ring
  have hI1 := integrable_psiA_shift_mul_nu hνc hF hν hB1 hT ha
  have hI2 : Integrable (fun τ => psiA cϱ p (τ - a) * (B + 2)) :=
    (psiA_shift_integrable hF a).mul_const _
  have hI3 : Integrable (fun τ => psiA cϱ p (τ - a) * Real.sqrt |τ - a| / Real.sqrt p.T) :=
    ((integrable_psiA_mul_sqrt hF).comp_sub_right a).div_const _
  have hΨ := integral_psiA_le hF
  have hS := integral_psiA_mul_sqrt_le hF
  have hmain : ∫ τ : ℝ, psiA cϱ p (τ - a) * |ν τ|
      ≤ (B + 2) * (2 * (4 + 2 * Real.log (cϱ * p.L / (4 * p.w))))
        + (2 * p.L + 4 * (cϱ / p.w)) / Real.sqrt p.T := by
    calc ∫ τ : ℝ, psiA cϱ p (τ - a) * |ν τ|
        ≤ ∫ τ : ℝ, (psiA cϱ p (τ - a) * (B + 2)
            + psiA cϱ p (τ - a) * Real.sqrt |τ - a| / Real.sqrt p.T) :=
          integral_mono hI1 (hI2.add hI3) hpt
      _ = ((B + 2) * ∫ r, psiA cϱ p r)
          + (∫ r, psiA cϱ p r * Real.sqrt |r|) / Real.sqrt p.T := by
          have hshift : ∫ τ : ℝ, psiA cϱ p (τ - a) * Real.sqrt |τ - a|
              = ∫ r : ℝ, psiA cϱ p r * Real.sqrt |r| :=
            integral_sub_right_eq_self (fun r => psiA cϱ p r * Real.sqrt |r|) a
          rw [integral_add hI2 hI3, integral_mul_const, integral_div, integral_psiA_shift,
            mul_comm, hshift]
      _ ≤ (B + 2) * (2 * (4 + 2 * Real.log (cϱ * p.L / (4 * p.w))))
          + (2 * p.L + 4 * (cϱ / p.w)) / Real.sqrt p.T :=
          add_le_add (mul_le_mul_of_nonneg_left hΨ (by positivity))
            (div_le_div_of_nonneg_right hS (Real.sqrt_nonneg _))
  -- the arithmetic:  4Ψ + (2L + 4c/w)/√T ≤ 5cB
  have hsT : 1 ≤ Real.sqrt p.T := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hT
  have hcw : cϱ / p.w ≤ cϱ := div_le_self hc hw1
  have htail : (2 * p.L + 4 * (cϱ / p.w)) / Real.sqrt p.T ≤ 2 * p.L + 4 * cϱ := by
    calc (2 * p.L + 4 * (cϱ / p.w)) / Real.sqrt p.T ≤ 2 * p.L + 4 * (cϱ / p.w) :=
          div_le_self (by positivity) hsT
      _ ≤ 2 * p.L + 4 * cϱ := by linarith
  have harg : 0 < cϱ * p.L / (4 * p.w) := by positivity
  have hlog : Real.log (cϱ * p.L / (4 * p.w)) ≤ cϱ * p.L / 4 - 1 := by
    have h1 := Real.log_le_sub_one_of_pos harg
    have h2 : cϱ * p.L / (4 * p.w) ≤ cϱ * p.L / 4 := by
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num) (by linarith)
    linarith
  -- endgame: 4Ψ + 2L + 4c ≤ 8 + 2cL + 2L + 4c ≤ 8 + 4c + 5cB ≤ 7cB  (Ψ ≤ 2 + cL/2, L ≤ 2B, 4 ≤ c, 4 ≤ B)
  have hcL : cϱ * p.L ≤ 2 * (cϱ * B) := by nlinarith
  have h2L : 2 * p.L ≤ cϱ * B := by nlinarith
  have h8c : 8 + 4 * cϱ ≤ 2 * (cϱ * B) := by nlinarith
  nlinarith [hmain, htail, hlog, hcL, h2L, h8c, hB0]
