-- Prove2me | solution 1 for Zeta23.PrimeSide.prop_trace
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T02:39:41.037961+00:00
-- url     : https://prove2.me/submissions/5bfc06b4-0dc9-471c-84d3-f99820c584b1

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
import Theorems.Thm_Zeta23_PrimeSide_lem_ends
import Theorems.Thm_Zeta23_PrimeSide_prop_cross_muP
import Theorems.Thm_Zeta23_PrimeSide_prop_mumu
import Theorems.Thm_Zeta23_PrimeSide_prop_trace_mu

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

lemma LocalHypsCore.L_pos (hF : LocalHypsCore cϱ p F) : 0 < p.L := by
  linarith [hF.eight_le_L]

lemma LocalHypsCore.b_pos (hF : LocalHypsCore cϱ p F) : 0 < F.b := by
  linarith [hF.b_ge_half]

lemma LocalHypsCore.a_pos (hF : LocalHypsCore cϱ p F) : 0 < F.a := hF.b_pos.trans_le hF.b_le_a


















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

theorem solution (hΓ : Zeta23.GammaFacts) (hcheb : Zeta23.ChebyshevMertens)
    (hlam : 0 < lam ∧ lam ≤ 1) (A : ℝ) :
    ∃ C : ℝ, EventuallyAtCore cϱ lam (fun p F => ∀ N : ℝ,
      |N - p.T * p.ell1 / (2 * π)| ≤ A * p.l →
      |trGtA p F - F.a * p.L * N| ≤ C * (p.L * Real.sqrt p.X)) := by
  obtain ⟨C₀, T₀, hC₀⟩ := prop_trace_mu cϱ lam hΓ hcheb hlam
  obtain ⟨Cμ, T₂, hCμ⟩ := hΓ.int_mu
  refine ⟨C₀ + |Cμ| + 2 * |A| / lam, max T₀ (max T₂ 1), fun p F hplam hT hF => ?_⟩
  intro N hN
  subst hplam
  have h0 := hC₀ p F rfl ((le_max_left _ _).trans hT) hF
  have hT2 : T₂ ≤ p.T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
  have hT1 : (1:ℝ) ≤ p.T := ((le_max_right _ _).trans (le_max_right _ _)).trans hT
  have hμint := hCμ p.T hT2
  have hL := hF.L_pos
  have hlam0 : 0 < p.lam := hlam.1
  have ha0 := hF.a_pos.le
  have ha1 := hF.a_le_one
  have hsX : 0 ≤ Real.sqrt p.X := Real.sqrt_nonneg _
  have hX1 : 1 ≤ Real.sqrt p.X := by
    rw [Real.le_sqrt' one_pos, one_pow]; exact Real.one_le_exp hL.le
  -- l ≤ (2/λ)√X  (since √X = e^{L/2} = e^{λl/2} ≥ λl/2)
  have hl0 : 0 ≤ p.l := zero_le_one.trans hF.one_le_l
  have hlX : p.l ≤ 2 / p.lam * Real.sqrt p.X := by
    have he : Real.sqrt p.X = Real.exp (p.lam * p.l / 2) := by
      rw [show p.X = Real.exp (p.lam * p.l) from rfl, ← Real.exp_half]
    rw [he, div_mul_eq_mul_div, le_div_iff₀ hlam0]
    have h1 := Real.add_one_le_exp (p.lam * p.l / 2)
    nlinarith
  -- assemble
  have e1 : |trGtA p F - F.a * p.L * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ|
      ≤ C₀ * (p.L * Real.sqrt p.X) := h0
  have e2 : |F.a * p.L * ((∫ τ in p.T..(2 * p.T), Zeta23.mu τ) - p.T * p.ell1 / (2 * π))|
      ≤ |Cμ| * (p.L * Real.sqrt p.X) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ F.a * p.L)]
    have h1 : |(∫ τ in p.T..(2 * p.T), Zeta23.mu τ) - p.T * p.ell1 / (2 * π)| ≤ |Cμ| := by
      refine hμint.trans ?_
      calc Cμ / p.T ≤ |Cμ| / p.T := by gcongr; exact le_abs_self _
        _ ≤ |Cμ| / 1 := by apply div_le_div_of_nonneg_left (abs_nonneg _) one_pos; exact hT1
        _ = |Cμ| := div_one _
    calc F.a * p.L * |(∫ τ in p.T..(2 * p.T), Zeta23.mu τ) - p.T * p.ell1 / (2 * π)|
        ≤ 1 * p.L * |Cμ| := by gcongr
      _ = p.L * |Cμ| := by ring
      _ ≤ (p.L * Real.sqrt p.X) * |Cμ| := by
          have := mul_le_mul_of_nonneg_left hX1 hL.le
          have h0' : 0 ≤ |Cμ| := abs_nonneg _
          nlinarith
      _ = |Cμ| * (p.L * Real.sqrt p.X) := by ring
  have e3 : |F.a * p.L * (p.T * p.ell1 / (2 * π) - N)|
      ≤ (2 * |A| / p.lam) * (p.L * Real.sqrt p.X) := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ F.a * p.L), abs_sub_comm]
    have hAl : A * p.l ≤ |A| * (2 / p.lam * Real.sqrt p.X) := by
      calc A * p.l ≤ |A| * p.l := mul_le_mul_of_nonneg_right (le_abs_self A) hl0
        _ ≤ |A| * (2 / p.lam * Real.sqrt p.X) :=
            mul_le_mul_of_nonneg_left hlX (abs_nonneg A)
    calc F.a * p.L * |N - p.T * p.ell1 / (2 * π)| ≤ 1 * p.L * (A * p.l) := by gcongr
      _ = p.L * (A * p.l) := by ring
      _ ≤ p.L * (|A| * (2 / p.lam * Real.sqrt p.X)) := mul_le_mul_of_nonneg_left hAl hL.le
      _ = (2 * |A| / p.lam) * (p.L * Real.sqrt p.X) := by field_simp
  calc |trGtA p F - F.a * p.L * N|
      = |(trGtA p F - F.a * p.L * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ)
          + F.a * p.L * ((∫ τ in p.T..(2 * p.T), Zeta23.mu τ) - p.T * p.ell1 / (2 * π))
          + F.a * p.L * (p.T * p.ell1 / (2 * π) - N)| := by ring_nf
    _ ≤ |trGtA p F - F.a * p.L * ∫ τ in p.T..(2 * p.T), Zeta23.mu τ|
          + |F.a * p.L * ((∫ τ in p.T..(2 * p.T), Zeta23.mu τ) - p.T * p.ell1 / (2 * π))|
          + |F.a * p.L * (p.T * p.ell1 / (2 * π) - N)| := abs_add_three _ _ _
    _ ≤ (C₀ + |Cμ| + 2 * |A| / p.lam) * (p.L * Real.sqrt p.X) := by linarith
