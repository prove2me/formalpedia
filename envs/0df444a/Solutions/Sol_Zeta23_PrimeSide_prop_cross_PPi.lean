-- Prove2me | solution 1 for Zeta23.PrimeSide.prop_cross_PPi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T03:01:32.618047+00:00
-- url     : https://prove2.me/submissions/d0b57dd0-fd80-45cc-ae1b-c48440ae123f

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
import Definitions.Def_Zeta23_PrimeSideA_EndsE2
import Definitions.Def_Zeta23_PrimeSideA_EndsNu
import Definitions.Def_Zeta23_PrimeSideB_PPKernel
import Theorems.Thm_Zeta23_PrimeSide_PX_abs_le
import Theorems.Thm_Zeta23_PrimeSide_abs_Mform_le
import Theorems.Thm_Zeta23_PrimeSide_lem_ends
import Theorems.Thm_Zeta23_PrimeSide_prop_cross_muP
import Theorems.Thm_Zeta23_PrimeSide_prop_mumu

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

lemma PX_continuous (X : ℝ) : Continuous (Zeta23.PX X) := by
  unfold Zeta23.PX
  fun_prop

/-! ### The large-T regime: elementary consequences of the hypotheses -/

section Regime
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

lemma Setting.X_pos (p : Setting) : 0 < p.X := Real.exp_pos _

/-- `l ≥ l₀` once `T ≥ 2π e^{l₀}`. -/
lemma Setting.le_l_of_T {p : Setting} {l₀ : ℝ} (hT : 2 * π * Real.exp l₀ ≤ p.T) : l₀ ≤ p.l := by
  have h2π : (0:ℝ) < 2 * π := by positivity
  have h : Real.exp l₀ ≤ p.T / (2 * π) := by rw [le_div_iff₀ h2π]; linarith
  calc l₀ = Real.log (Real.exp l₀) := (Real.log_exp _).symm
    _ ≤ Real.log (p.T / (2 * π)) := Real.log_le_log (Real.exp_pos _) h
    _ = p.l := rfl



/-- `X ≥ x₀` once `T ≥ 2π exp(|x₀|/λ)` (`X = (T/2π)^λ → ∞`; this is the "T ≥ T₀(λ)" of §5). -/
lemma Setting.le_X_of_T {p : Setting} (hlam : 0 < p.lam) {x₀ : ℝ}
    (hT : 2 * π * Real.exp (|x₀| / p.lam) ≤ p.T) : x₀ ≤ p.X := by
  have hl : |x₀| / p.lam ≤ p.l := Setting.le_l_of_T hT
  have h1 : |x₀| ≤ p.lam * p.l := by rwa [div_le_iff₀' hlam] at hl
  calc x₀ ≤ |x₀| := le_abs_self _
    _ ≤ p.lam * p.l := h1
    _ ≤ Real.exp (p.lam * p.l) := by linarith [Real.add_one_le_exp (p.lam * p.l)]
    _ = p.X := rfl







/-! ### Window-generic core of the taper hypotheses (paper §7.1 [subsec:MT])

"Nothing in Sections 4–5 used that φ is flat-topped" — except the [eq:gbounds] plateau lower
bound and the [eq:abdef] lower bound on b.  LocalHypsCore is LocalHyps minus exactly those two
facts, with the window-generic replacements g_nonneg and b_ge_half (both hold for the
Montgomery–Taylor window of [thm:D], which does not satisfy LocalHyps).  Surviving field names
are identical to LocalHyps'.  The window-generic §5 results can be re-typed over this
structure; the structure itself is purely additive. -/






/-! Core copies of the LocalHyps helper lemmas (same names under the Core namespace). -/

lemma LocalHypsCore.eight_le_L (hF : LocalHypsCore cϱ p F) : 8 ≤ p.L := by
  linarith [hF.one_le_w, hF.w_le]

lemma LocalHypsCore.L_pos (hF : LocalHypsCore cϱ p F) : 0 < p.L := by
  linarith [hF.eight_le_L]



lemma LocalHypsCore.integral_Phi_sq_le (hF : LocalHypsCore cϱ p F) :
    ∫ x, F.Phi x ^ 2 ≤ 2 * π * p.L := by
  rw [hF.Phi_sq_integral]
  have hb1 : F.b ≤ 1 := hF.b_le_a.trans hF.a_le_one
  have hL := hF.L_pos
  calc 2 * π * F.b * p.L = (2 * π * p.L) * F.b := by ring
    _ ≤ (2 * π * p.L) * 1 := by gcongr
    _ = 2 * π * p.L := mul_one _

lemma LocalHypsCore.PiX_le_on_I (hF : LocalHypsCore cϱ p F) (hT : 0 < p.T) :
    ∀ τ ∈ Set.Icc p.T (2 * p.T), |Zeta23.PiX p.X τ| ≤ 3 * Real.sqrt p.X / p.T := by
  intro τ hτ
  refine (hF.PiX_bound τ).trans ?_
  apply div_le_div_of_nonneg_left (by positivity) hT
  rw [abs_of_nonneg (by linarith [hτ.1])]
  linarith [hτ.1]
















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

-- from Zeta23.PrimeSideA
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization of
  "More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/

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

section Results

variable (cϱ lam : ℝ)
/-! ## [prop:trace]  (§5.2) -/



/-! ## [lem:ends]  (§5.3), with [eq:Kdef], [eq:trG2int], [eq:Kbounds] -/

-- **[lem:ends]** is proved in Zeta23/PrimeSideA/Ends.lean:
-- `Zeta23.PrimeSide.lem_ends` (§5.3) — imported by this module.

/-! ## [eq:Msplit]  (§5.4) -/


/-! ## [prop:mumu]  (§5.4) -/

/-! **[prop:mumu]**, first form (§5.4, verbatim): `𝓜[μ,μ] = 2πbL ∫_T^{2T} μ² + O(l² log L)`.
(The second form `= (bLTℓ₁²/2π)(1+O(l⁻²)) + O(l² log L)` follows with [eq:muints] and is taken in
PrimeSideB.)  We write `log L` as in the paper; note `log L ≤ log l` since `λ ≤ 1`. -/
-- **[prop:mumu]** is proved in Zeta23/PrimeSideA/MuMu.lean:
-- `Zeta23.PrimeSide.prop_mumu` — imported by this module, so available here under the same name.

/-! ## [prop:cross]  (§5.4) -/

-- **[prop:cross] (i)** is proved in Zeta23/PrimeSideA/CrossMuP.lean:
-- `Zeta23.PrimeSide.prop_cross_muP` (§5.4: 𝓜[μ,P_X] ≪ l√X) — imported by this module.




end Results

/-!
## Contents
Proved in this file:
* eq_Msplit — [eq:Msplit]
* prop_cross_muPi / _PPi / _PiPi — [prop:cross] (ii)(iii)(iv)
* prop_trace_mu, prop_trace — **[prop:trace]** (μ-form and the paper's aL·N(T,2T) + O(L√X) form)
Proved in child files, imported here:
* prop_mumu      — [prop:mumu]     — Zeta23/PrimeSideA/MuMu.lean
* prop_cross_muP — [prop:cross](i) — Zeta23/PrimeSideA/CrossMuP.lean
* lem_ends       — [lem:ends]      — Zeta23/PrimeSideA/Ends.lean
-/

end PrimeSide
end Zeta23
end
open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction
open Zeta23
open PrimeSide
variable (cϱ lam : ℝ)

theorem solution (_hΓ : Zeta23.GammaFacts) (hcheb : Zeta23.ChebyshevMertens)
    (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F =>
      |Mform F.Phi p.T (Zeta23.PX p.X) (Zeta23.PiX p.X)| ≤ C * (p.L * p.X)) := by
  obtain ⟨x₀, hx₀⟩ := PX_abs_le hcheb
  refine ⟨6 * π, max (2 * π * Real.exp (|x₀| / lam)) 1, fun p F hplam hT hF => ?_⟩
  have hT0 : 0 < p.T := by linarith [le_max_right (2 * π * Real.exp (|x₀| / lam)) 1]
  have hX : x₀ ≤ p.X := Setting.le_X_of_T (hplam ▸ hlam.1) (by rw [hplam]; exact (le_max_left _ _).trans hT)
  have hP : ∀ τ ∈ Set.Icc p.T (2 * p.T), |Zeta23.PX p.X τ| ≤ Real.sqrt p.X := fun τ _ => hx₀ _ hX τ
  have hPi := hF.PiX_le_on_I hT0
  have h := abs_Mform_le hT0.le hF.Phi_contDiff.continuous (PX_continuous p.X) hF.PiX_cont
    hF.Phi_sq_integrable hP hPi
  have hX0 := hF.integral_Phi_sq_le
  calc |Mform F.Phi p.T (Zeta23.PX p.X) (Zeta23.PiX p.X)|
      ≤ Real.sqrt p.X * (3 * Real.sqrt p.X / p.T) * (p.T * ∫ x, F.Phi x ^ 2) := h
    _ ≤ Real.sqrt p.X * (3 * Real.sqrt p.X / p.T) * (p.T * (2 * π * p.L)) := by gcongr
    _ = 6 * π * (p.L * (Real.sqrt p.X) ^ 2) := by field_simp; ring
    _ = 6 * π * (p.L * p.X) := by rw [Real.sq_sqrt p.X_pos.le]
