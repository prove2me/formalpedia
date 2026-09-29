-- Prove2me | solution 1 for Zeta23.PrimeSide.mu_increment_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T03:17:24.885759+00:00
-- url     : https://prove2.me/submissions/8f2ac8de-50df-4db6-94cd-5e7c7699e5e4

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs
import Theorems.Thm_Zeta23_PrimeSide_mu_linear_bound

-- from Zeta23.PrimeSideA.Basic
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
open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction
open Zeta23
open PrimeSide
variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

theorem solution (hΓ : Zeta23.GammaFacts) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t : ℝ, 2 ≤ t → ∀ r : ℝ,
      |Zeta23.mu (t + r) - Zeta23.mu t| ≤ (K * |r| + 10 * r ^ 2) / t := by
  obtain ⟨C₁, hC₁⟩ := hΓ.deriv_bound
  obtain ⟨M, hM0, hM⟩ := mu_linear_bound hΓ
  refine ⟨max (2 * |C₁|) (4 * M), le_max_of_le_right (by positivity), fun t ht r => ?_⟩
  have ht0 : 0 < t := by linarith
  rw [le_div_iff₀ ht0]
  rcases le_or_gt |r| (t / 2) with hr | hr
  · -- mean value theorem on [t/2, 3t/2]
    have hmvt : ‖Zeta23.mu (t + r) - Zeta23.mu t‖ ≤ (2 * |C₁| / t) * ‖(t + r) - t‖ := by
      apply Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.Icc (t / 2) (3 * t / 2))
      · intro x _; exact hΓ.smooth.contDiffAt.differentiableAt (by simp)
      · intro x hx
        have hx1 : 1 ≤ |x| := by rw [abs_of_pos (by linarith [hx.1])]; linarith [hx.1]
        calc ‖deriv Zeta23.mu x‖ = |deriv Zeta23.mu x| := Real.norm_eq_abs _
          _ ≤ C₁ / |x| := hC₁ x hx1
          _ ≤ |C₁| / |x| := by gcongr; exact le_abs_self _
          _ ≤ |C₁| / (t / 2) := by
              apply div_le_div_of_nonneg_left (abs_nonneg _) (by linarith)
              rw [abs_of_pos (by linarith [hx.1])]; exact hx.1
          _ = 2 * |C₁| / t := by field_simp
      · exact convex_Icc _ _
      · constructor <;> linarith
      · constructor <;> linarith [le_abs_self r, neg_abs_le r]
    simp only [add_sub_cancel_left, Real.norm_eq_abs] at hmvt
    calc |Zeta23.mu (t + r) - Zeta23.mu t| * t ≤ (2 * |C₁| / t * |r|) * t := by gcongr
      _ = 2 * |C₁| * |r| := by field_simp
      _ ≤ max (2 * |C₁|) (4 * M) * |r| + 10 * r ^ 2 := by
          nlinarith [le_max_left (2 * |C₁|) (4 * M), abs_nonneg r, sq_nonneg r]
  · -- |r| > t/2: crude bound, absorbed using t < 2|r|
    have h1 : |Zeta23.mu (t + r) - Zeta23.mu t| ≤ 2 * M + 5 * |r| := by
      calc |Zeta23.mu (t + r) - Zeta23.mu t| ≤ |Zeta23.mu (t + r)| + |Zeta23.mu t| := abs_sub _ _
        _ ≤ (M + |t + r|) + (M + |t|) := add_le_add (hM _) (hM _)
        _ ≤ (M + (|t| + |r|)) + (M + |t|) := by linarith [abs_add_le t r]
        _ = 2 * M + 2 * |t| + |r| := by ring
        _ ≤ 2 * M + 5 * |r| := by rw [abs_of_pos ht0]; linarith
    calc |Zeta23.mu (t + r) - Zeta23.mu t| * t ≤ (2 * M + 5 * |r|) * t := by gcongr
      _ ≤ (2 * M + 5 * |r|) * (2 * |r|) := by gcongr; linarith
      _ = 4 * M * |r| + 10 * |r| ^ 2 := by ring
      _ = 4 * M * |r| + 10 * r ^ 2 := by rw [sq_abs]
      _ ≤ max (2 * |C₁|) (4 * M) * |r| + 10 * r ^ 2 := by
          nlinarith [le_max_right (2 * |C₁|) (4 * M), abs_nonneg r]
