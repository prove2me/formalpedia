-- Prove2me | solution 1 for Zeta23.PrimeSide.P_part_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T06:39:51.452712+00:00
-- url     : https://prove2.me/submissions/16a8bbfa-a09a-454a-8826-2a5fbb950824

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

-- from Zeta23.PrimeSideA.Defs
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23 — prime side (paper §5 [sec:prime]) — ABSTRACT LAYER & SHARED DEFINITIONS
for PrimeSideA.lean / PrimeSideB.lean.

Bracketed labels and section numbers (§5.2, …) are as in the paper
"More than two thirds of the zeros of the Riemann zeta function lie on the critical line".

SEAM between PrimeSideA.lean and PrimeSideB.lean:
  * The seam object is the symmetric bilinear form
        𝓜[u₁,u₂] := ∬_{I×I} Φ(τ−τ')² u₁(τ) u₂(τ') dτ dτ',   I = [T,2T]          (§5.4)
    spelled here LITERALLY as `Mform Φ T u₁ u₂` below, and 𝓜 := 𝓜[ν_X,ν_X] = `MtotalA`.
  * PrimeSideA.lean : [prop:trace] tr G̃ = aL·N(T,2T)+O(L√X);
      [eq:trG2int]+[eq:Kbounds]+[lem:ends] tr G̃² = 𝓜 + O(L·l·log l·(l²+X));
      [eq:Msplit] (6-term expansion of 𝓜); [prop:mumu]; [prop:cross] (four bounds).
  * PrimeSideB.lean : [prop:PP] incl. 𝒟/𝒪₁/𝒪₂ and the g-sandwich via H-cheb [eq:cheb2];
      [thm:traces] = [eq:tr1],[eq:tr2],[eq:ratio] assembling A's five results + prop:PP + H-Γ [eq:muints] + H-RvM.
  * Error-term shape everywhere: ∃ C T₀ (allowed to depend on the profile constants and on λ),
      ∀ T ≥ T₀, |lhs − main| ≤ C·(error expression).  No filters / IsBigO until the final liminf wrapper.

ABSTRACT LAYER.  §5 is a computation about the functions φ̂, Φ, μ, Π_X, P_X on the REAL line
using only a short list of facts about them ([eq:psidef], [eq:abdef], [eq:gbounds], [eq:Phi2FT],
[lem:poisson], [eq:mufacts], [eq:PiPfacts], [lem:cheb]).  We therefore prove §5 for ABSTRACT data
(`Setting` = the scalars T, λ, w;  `LocalFun` = the taper data φ̂, Φ, A_φ, g, a, b) subject
to exactly those facts (hypothesis structures in PrimeSideA.lean), and a thin bridge
(Zeta23/PrimeSideA/Bridge.lean) instantiates it with the
concrete objects of Zeta23/Defs.lean: `Zeta23.Params.phiHatR`, `.PhiR`, `.a`, `.b`, `.g`, `.Aphi`,
so that `trGtA` below becomes `Zeta23.Params.trGtilde` etc.  Names in this
layer carry a trailing `A` (abstract) where they would otherwise clash with Zeta23/Defs.lean.
The closed-form, ζ-free objects `Zeta23.l`, `Zeta23.ell1`, `Zeta23.mu` [eq:mudef], `Zeta23.PiX` [eq:Pidef],
`Zeta23.PX` [eq:Pdef], `Zeta23.nuX` [eq:nudef] are used DIRECTLY from Zeta23/Defs.lean, and the analytic
inputs H-Γ / H-cheb are Zeta23/Hypotheses.lean's `GammaFacts` / `ChebyshevMertens` verbatim, so the
statements here are literally about the official objects of Zeta23/Defs.lean; only the taper enters
abstractly.

The prime side is ζ-free: N(T,2T) enters only as an abstract real together
with [eq:RvM].

FOURIER CONVENTION: paper f̂(τ) := ∫ f(u) e^{iτu} du (§1.4) = `Zeta23.paperFT`.  On
this side we only meet φ̂ and Φ := (φ²)^ on ℝ, where they are real and even; we carry them as
functions ℝ → ℝ (= `phiHatR`, `PhiR` of Defs.lean).
-/


noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction

namespace Zeta23
namespace PrimeSide

/-! ## Scalars of the abstract setting  [§1 Notation, §1.4; eq:wrange; eq:fk] -/


namespace Setting
variable (p : Setting)


end Setting

/-! ## The prime-power sum: notation of §5 for `Zeta23.PX` [eq:Pdef, §2.1] -/


/-- `Zeta23.PX` in the `a_n, y_n` notation of §5: `P_X(τ) = −(1/π) Σ_{n≤X} a_n cos(τ y_n)`. -/
lemma PX_eq (X τ : ℝ) :
    Zeta23.PX X τ = -(1 / Real.pi) * ∑ n ∈ primeRange X, acoef n * Real.cos (τ * ycoef n) := rfl

/-! ## Abstract functional data

In the concrete instantiation `phiHat, Phi, Aphi, g, a, b` are Zeta23/Defs.lean's `P.phiHatR T`,
`P.PhiR T`, `P.Aphi T`, `P.g T`, `P.a T`, `P.b T` ([eq:phidef], [eq:abdef], [eq:PhigA]). -/


variable (p : Setting) (F : LocalFun)





/-! ## The seam: the bilinear form 𝓜[·,·]  [§5 "Evaluation of 𝓜", §5.4] -/



end PrimeSide
end Zeta23
end
end

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

lemma PX_continuous (X : ℝ) : Continuous (Zeta23.PX X) := by
  unfold Zeta23.PX
  fun_prop

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








lemma LocalHypsCore.phiHat_sq_mul_integrable_of_bdd (hF : LocalHypsCore cϱ p F) {g : ℝ → ℝ}
    (hg : Continuous g) {c : ℝ} (hc : ∀ x, |g x| ≤ c) :
    Integrable (fun r => F.phiHat r ^ 2 * g r) := by
  have := hF.phiHat_sq_integrable.bdd_mul hg.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by rw [Real.norm_eq_abs]; exact hc x))
  simpa only [mul_comm] using this














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

theorem solution (hF : LocalHypsCore cϱ p F) (t : ℝ) :
    Integrable (fun r => F.phiHat r ^ 2 * Zeta23.PX p.X (t + r)) := by
  refine hF.phiHat_sq_mul_integrable_of_bdd ((PX_continuous p.X).comp (continuous_const_add t))
    (c := 1 / Real.pi * ∑ n ∈ primeRange p.X, acoef n) (fun x => ?_)
  simp only [PX_eq]
  rw [abs_mul, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 1 / Real.pi)]
  gcongr
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  have ha : 0 ≤ acoef n := div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  rw [abs_mul, abs_of_nonneg ha]
  calc acoef n * |Real.cos ((t + x) * ycoef n)| ≤ acoef n * 1 := by
        gcongr; exact Real.abs_cos_le_one _
    _ = acoef n := mul_one _
