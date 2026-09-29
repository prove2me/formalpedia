-- Prove2me | solution 1 for Zeta23.PrimeSide.prop_mumu
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T03:11:16.656178+00:00
-- url     : https://prove2.me/submissions/4d94657f-1f4e-4635-a564-6f6388271c01

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
import Definitions.Def_Zeta23_PrimeSideB_PPKernel
import Theorems.Thm_Zeta23_PrimeSide_mu_abs_le_l
import Theorems.Thm_Zeta23_PrimeSide_mu_increment_bound
import Theorems.Thm_Zeta23_PrimeSide_mumu_core

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

lemma LocalHypsCore.eight_le_L (hF : LocalHypsCore cϱ p F) : 8 ≤ p.L := by
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

-- from Zeta23.PrimeSideA.MuMu
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/PrimeSideA/MuMu.lean

[prop:mumu] (paper §5.4): 𝓜[μ,μ] = 2πbL ∫_T^{2T} μ² + O(l² log L).

Paper proof, as implemented here:
  * shear τ = τ' + x (`sqIntegral_shear`):
      𝓜[μ,μ] = ∫_ℝ Φ(x)² (∫_{I∩(I−x)} μ(x+τ')μ(τ') dτ') dx;
  * Lipschitz step "μ(τ)=μ(τ')+O(|τ−τ'|/T)" (via `mu_increment_bound`'s (K|r|+10r²)/t):
      |∫_{Ix}(μ(x+τ')−μ(τ'))μ(τ')| ≤ l(K|x| + 10x²)   (window length ≤ T, τ' ≥ T);
  * completing ∫_{Ix} to ∫_I ("∫_{I−τ'}Φ² = 2πbL − tails"):
      |∫_{I∖Ix} μ²| ≤ l²·|x|   (vol(I∖Ix) = min(|x|,T));
  * ∫Φ²|x| ≤ 8 + 8log(cϱL/4w) ≪ log L  [eq:psiints]  and  ∫Φ²x² ≤ 8 + 2(cϱ/w)² = O(1).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Real Set
open scoped BigOperators

namespace Zeta23
namespace PrimeSide

variable {cϱ : ℝ}

section Core

variable {p : Setting} {F : LocalFun}



end Core

/-! ## [prop:mumu] -/

variable (cϱ lam : ℝ)


end PrimeSide
end Zeta23
end
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Real Set
open scoped BigOperators
open Zeta23
open PrimeSide
variable {cϱ : ℝ}
variable (cϱ lam : ℝ)
set_option linter.unusedVariables false

theorem solution (hΓ : Zeta23.GammaFacts) (hcheb : Zeta23.ChebyshevMertens)
    (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F =>
      |Mform F.Phi p.T Zeta23.mu Zeta23.mu
          - 2 * π * F.b * p.L * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ ^ 2|
        ≤ C * (p.l ^ 2 * Real.log p.L)) := by
  obtain ⟨K, hK0, hKinc⟩ := mu_increment_bound hΓ
  obtain ⟨T₀μ, hT₀μ⟩ := mu_abs_le_l hΓ
  refine ⟨(1 + K) * (12 + 4 * max 0 (Real.log cϱ)) + 5 * (8 + 2 * cϱ ^ 2),
    max T₀μ 2, fun p F hplam hT hF => ?_⟩
  have hT2 : 2 ≤ p.T := le_trans (le_max_right _ _) hT
  have hμl := hT₀μ p (le_trans (le_max_left _ _) hT)
  have hcore := mumu_core hΓ hF hT2 hμl hK0 hKinc
  have hI1 := hF.integral_Phi_sq_mul_abs_le
  have hI2 := hF.integral_Phi_sq_mul_sq_le
  have hL8 : 8 ≤ p.L := hF.eight_le_L
  have hlog2 : 2 ≤ Real.log p.L := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have h1 := Real.exp_one_lt_d9
    calc Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      _ ≤ 2.7182818286 * 2.7182818286 := by nlinarith [Real.exp_pos 1]
      _ ≤ 8 := by norm_num
      _ ≤ p.L := hL8
  have hlogpos : 0 < Real.log p.L := by linarith
  have hcϱ4 : 4 ≤ cϱ := hF.four_le_cϱ
  have hw1 : 1 ≤ p.w := hF.one_le_w
  have hl1 : 1 ≤ p.l := hF.one_le_l
  have hm0 : 0 ≤ max 0 (Real.log cϱ) := le_max_left _ _
  have hlogbound : Real.log (cϱ * p.L / (4 * p.w)) ≤ max 0 (Real.log cϱ) + Real.log p.L := by
    calc Real.log (cϱ * p.L / (4 * p.w)) ≤ Real.log (cϱ * p.L) := by
          apply Real.log_le_log (by positivity)
          apply div_le_self (by positivity)
          linarith
      _ = Real.log cϱ + Real.log p.L := Real.log_mul (by positivity) (by positivity)
      _ ≤ max 0 (Real.log cϱ) + Real.log p.L := by
          have := le_max_right (0 : ℝ) (Real.log cϱ)
          linarith
  have hA : ∫ x, F.Phi x ^ 2 * |x| ≤ (12 + 4 * max 0 (Real.log cϱ)) * Real.log p.L := by
    refine hI1.trans ?_
    have h8 : 8 + 8 * Real.log (cϱ * p.L / (4 * p.w))
        ≤ 8 + 8 * (max 0 (Real.log cϱ) + Real.log p.L) := by linarith
    refine h8.trans ?_
    nlinarith [mul_nonneg hm0 (by linarith : (0 : ℝ) ≤ Real.log p.L - 2)]
  have hB : ∫ x, F.Phi x ^ 2 * x ^ 2 ≤ 8 + 2 * cϱ ^ 2 := by
    refine hI2.trans ?_
    have hdiv : cϱ / p.w ≤ cϱ := div_le_self (by linarith) hw1
    have hdivnn : 0 ≤ cϱ / p.w := by positivity
    nlinarith
  have hI1nn : 0 ≤ ∫ x, F.Phi x ^ 2 * |x| := integral_nonneg fun x => by positivity
  have hI2nn : 0 ≤ ∫ x, F.Phi x ^ 2 * x ^ 2 := integral_nonneg fun x => by positivity
  refine hcore.trans ?_
  have hstep : (1 + K) * p.l ^ 2 * (∫ x, F.Phi x ^ 2 * |x|)
        + 10 * p.l * ∫ x, F.Phi x ^ 2 * x ^ 2
      ≤ (1 + K) * p.l ^ 2 * ((12 + 4 * max 0 (Real.log cϱ)) * Real.log p.L)
        + 10 * p.l * (8 + 2 * cϱ ^ 2) := by
    gcongr
  refine hstep.trans ?_
  have hlt : (0 : ℝ) ≤ p.l * Real.log p.L - 2 := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ p.l - 1) (by linarith : (0 : ℝ) ≤ Real.log p.L)]
  have h82 : (0 : ℝ) ≤ 8 + 2 * cϱ ^ 2 := by positivity
  have hfin : 10 * p.l * (8 + 2 * cϱ ^ 2)
      ≤ 5 * (8 + 2 * cϱ ^ 2) * (p.l ^ 2 * Real.log p.L) := by
    nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ p.l) h82) hlt]
  nlinarith [hfin]
