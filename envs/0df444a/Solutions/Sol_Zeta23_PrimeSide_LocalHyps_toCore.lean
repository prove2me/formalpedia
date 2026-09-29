-- Prove2me | solution 1 for Zeta23.PrimeSide.LocalHyps.toCore
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T06:33:43.043172+00:00
-- url     : https://prove2.me/submissions/6a8387b0-cb61-47ad-a621-abddb4c137ca

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






lemma LocalHyps.eight_le_L (hF : LocalHyps cϱ p F) : 8 ≤ p.L := by
  linarith [hF.one_le_w, hF.w_le]

lemma LocalHyps.L_pos (hF : LocalHyps cϱ p F) : 0 < p.L := by linarith [hF.eight_le_L]





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

theorem solution {cϱ : ℝ} {p : Setting} {F : LocalFun} (hF : LocalHyps cϱ p F) :
    LocalHypsCore cϱ p F where
  four_le_cϱ := hF.four_le_cϱ
  lam_pos := hF.lam_pos
  lam_le_one := hF.lam_le_one
  one_le_w := hF.one_le_w
  w_le := hF.w_le
  one_le_l := hF.one_le_l
  phiHat_cont := hF.phiHat_cont
  phiHat_even := hF.phiHat_even
  phiHat_le_L := hF.phiHat_le_L
  phiHat_le_inv := hF.phiHat_le_inv
  phiHat_le_sq := hF.phiHat_le_sq
  phiHat_sq_integrable := hF.phiHat_sq_integrable
  phiHat_sq_mul_abs_integrable := hF.phiHat_sq_mul_abs_integrable
  integral_phiHat_sq_mul_abs_le := hF.integral_phiHat_sq_mul_abs_le
  phiHat_sq_mul_sq_integrable := hF.phiHat_sq_mul_sq_integrable
  integral_phiHat_sq_mul_sq_le := hF.integral_phiHat_sq_mul_sq_le
  phiHat_sq_integral := hF.phiHat_sq_integral
  phiHat_sq_fourier := hF.phiHat_sq_fourier
  g_nonneg := fun y => le_trans (le_max_right _ _) (hF.g_lower y)
  g_le_Aphi := hF.g_le_Aphi
  Aphi_le := hF.Aphi_le
  Phi_contDiff := hF.Phi_contDiff
  Phi_even := hF.Phi_even
  Phi_le_L := hF.Phi_le_L
  Phi_le_inv := hF.Phi_le_inv
  Phi_le_sq := hF.Phi_le_sq
  Phi_sq_integrable := hF.Phi_sq_integrable
  Phi_sq_mul_abs_integrable := hF.Phi_sq_mul_abs_integrable
  integral_Phi_sq_mul_abs_le := hF.integral_Phi_sq_mul_abs_le
  Phi_sq_mul_sq_integrable := hF.Phi_sq_mul_sq_integrable
  integral_Phi_sq_mul_sq_le := hF.integral_Phi_sq_mul_sq_le
  Phi_zero := hF.Phi_zero
  Phi_sq_integral := hF.Phi_sq_integral
  Phi_sq_fourier := hF.Phi_sq_fourier
  poisson := hF.poisson
  b_ge_half := by
    have h1 : 2 * p.w / p.L ≤ 1 / 4 := by
      rw [div_le_iff₀ hF.L_pos]
      linarith [hF.w_le]
    linarith [hF.b_lower]
  b_le_a := hF.b_le_a
  a_le_one := hF.a_le_one
  psi_integrable := hF.psi_integrable
  psi_sq_integrable := hF.psi_sq_integrable
  integral_psi_Ioi_le := hF.integral_psi_Ioi_le
  integral_psi_sq_le := hF.integral_psi_sq_le
  phiHat_le_psi := hF.phiHat_le_psi
  Phi_le_psi := hF.Phi_le_psi
  PiX_cont := hF.PiX_cont
  PiX_bound := hF.PiX_bound
