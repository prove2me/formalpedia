-- Prove2me | solution 1 for Zeta23.PrimeSide.riemann_sum_monotone
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T02:51:23.572542+00:00
-- url     : https://prove2.me/submissions/f618e37e-3b30-45ad-9882-e76b1445ff01

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

theorem solution {μ : ℝ → ℝ} {T h : ℝ} (hh : 0 < h) (hhT : h ≤ T)
    (hmono : MonotoneOn μ (Set.Ici (T - h))) (hnonneg : ∀ x, T - h ≤ x → 0 ≤ μ x) :
    |h * ∑ k ∈ Finset.range ⌊T / h⌋₊, μ (T + k * h) - ∫ x in T..(2 * T), μ x|
      ≤ 2 * h * μ (2 * T) := by
  have hT : 0 < T := hh.trans_le hhT
  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = ⌊T / h⌋₊ := ⟨_, rfl⟩
  rw [← hd]
  have hdh : (d : ℝ) * h ≤ T := by
    have := Nat.floor_le (div_nonneg hT.le hh.le); rw [← hd] at this
    rwa [le_div_iff₀ hh] at this
  have hdh' : T < (d + 1 : ℝ) * h := by
    have := Nat.lt_floor_add_one (T / h); rw [← hd] at this
    rwa [div_lt_iff₀ hh] at this
  have hd1 : 1 ≤ d := by
    have : (1:ℝ) ≤ T / h := by rw [le_div_iff₀ hh]; linarith
    exact_mod_cast (Nat.one_le_floor_iff _).2 this |>.trans_eq hd.symm
  -- rescaled function
  set f : ℝ → ℝ := fun s => μ (T + h * s) with hf
  have hfmono : ∀ a : ℝ, -1 ≤ a → MonotoneOn f (Set.Ici a) := by
    intro a ha x hx y hy hxy
    apply hmono
    · simp only [Set.mem_Ici] at hx ⊢; nlinarith
    · simp only [Set.mem_Ici] at hy ⊢; nlinarith
    · nlinarith
  have hμint : ∀ a b : ℝ, T - h ≤ a → T - h ≤ b → IntervalIntegrable μ volume a b := by
    intro a b ha hb
    apply MonotoneOn.intervalIntegrable
    exact hmono.mono (by
      intro x hx; simp only [Set.mem_Ici]
      rcases Set.mem_uIcc.1 hx with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith)
  -- change of variables: ∫_0^a f = h⁻¹ ∫_T^{T+ha} μ
  have hcov : ∀ a : ℝ, ∫ s in (0:ℝ)..a, f s = h⁻¹ * ∫ x in T..(T + h * a), μ x := by
    intro a
    have e := intervalIntegral.integral_comp_mul_add (a := 0) (b := a) μ hh.ne' T
    rw [mul_zero, zero_add, smul_eq_mul, show h * a + T = T + h * a by ring] at e
    rw [← e]
    refine intervalIntegral.integral_congr fun s _ => ?_
    simp only [hf]; ring_nf
  -- upper bound: h Σ_{k<d} μ(T+kh) ≤ ∫_T^{T+dh} μ ≤ ∫_T^{2T} μ
  have hup : h * ∑ k ∈ Finset.range d, μ (T + k * h) ≤ ∫ x in T..(2 * T), μ x := by
    have h1 := (hfmono 0 (by norm_num)).mono
      (show Set.Icc (0:ℝ) (0 + d) ⊆ Set.Ici 0 from fun x hx => hx.1) |>.sum_le_integral
    simp only [zero_add] at h1
    rw [hcov] at h1
    have h2 : ∑ k ∈ Finset.range d, μ (T + k * h) = ∑ i ∈ Finset.range d, f (i : ℝ) := by
      refine Finset.sum_congr rfl fun k _ => ?_; simp [hf, mul_comm]
    rw [h2]
    have h3 : h * ∑ i ∈ Finset.range d, f (i : ℝ) ≤ ∫ x in T..(T + h * d), μ x := by
      have := mul_le_mul_of_nonneg_left h1 hh.le
      rwa [← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul] at this
    refine h3.trans ?_
    -- ∫_T^{T+hd} ≤ ∫_T^{2T} since μ ≥ 0 on [T+hd, 2T]
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hμint T (T + h * d) (by linarith) (by nlinarith))
      (hμint (T + h * d) (2 * T) (by nlinarith) (by linarith))
    rw [← hsplit]
    have : 0 ≤ ∫ x in (T + h * d)..(2 * T), μ x :=
      intervalIntegral.integral_nonneg (by nlinarith) fun x hx => hnonneg x (by nlinarith [hx.1])
    linarith
  -- lower bound
  have hlo : (∫ x in T..(2 * T), μ x) - 2 * h * μ (2 * T)
      ≤ h * ∑ k ∈ Finset.range d, μ (T + k * h) := by
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, (Nat.sub_add_cancel hd1).symm⟩
    have h1 := (hfmono 0 (by norm_num)).mono
      (show Set.Icc (0:ℝ) (0 + d') ⊆ Set.Ici 0 from fun x hx => hx.1) |>.integral_le_sum
    simp only [zero_add] at h1
    rw [hcov] at h1
    -- Σ_{i<d'} f(i+1) ≤ Σ_{k<d'+1} μ(T+kh)  (drop k = 0 term, which is ≥ 0)
    have h2 : ∑ i ∈ Finset.range d', f ((i + 1 : ℕ) : ℝ)
        ≤ ∑ k ∈ Finset.range (d' + 1), μ (T + k * h) := by
      rw [Finset.sum_range_succ']
      have : ∑ i ∈ Finset.range d', f ((i + 1 : ℕ) : ℝ)
          = ∑ k ∈ Finset.range d', μ (T + ((k + 1 : ℕ) : ℝ) * h) := by
        refine Finset.sum_congr rfl fun k _ => ?_; simp [hf, mul_comm]
      rw [this]
      have : 0 ≤ μ (T + ((0:ℕ):ℝ) * h) := hnonneg _ (by simp; linarith)
      linarith
    have h3 : (∫ x in T..(T + h * d'), μ x) ≤ h * ∑ k ∈ Finset.range (d' + 1), μ (T + k * h) := by
      have := mul_le_mul_of_nonneg_left (h1.trans h2) hh.le
      rwa [← mul_assoc, mul_inv_cancel₀ hh.ne', one_mul] at this
    refine le_trans ?_ h3
    -- ∫_T^{2T} μ − ∫_T^{T+hd'} μ = ∫_{T+hd'}^{2T} μ ≤ (2T − T − hd')·μ(2T) ≤ 2h μ(2T)
    push_cast at hdh hdh'
    have hlen : 2 * T - (T + h * d') ≤ 2 * h := by nlinarith
    have hlen0 : T + h * d' ≤ 2 * T := by nlinarith
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hμint T (T + h * d') (by linarith) (by nlinarith))
      (hμint (T + h * d') (2 * T) (by nlinarith) (by linarith))
    rw [← hsplit]
    have hμ2T : 0 ≤ μ (2 * T) := hnonneg _ (by linarith)
    have : ∫ x in (T + h * d')..(2 * T), μ x ≤ 2 * h * μ (2 * T) := by
      calc ∫ x in (T + h * d')..(2 * T), μ x
          ≤ ∫ x in (T + h * d')..(2 * T), μ (2 * T) := by
            apply intervalIntegral.integral_mono_on hlen0
              (hμint _ _ (by nlinarith) (by linarith)) intervalIntegrable_const
            intro x hx
            exact hmono (by simp only [Set.mem_Ici]; nlinarith [hx.1])
              (by simp only [Set.mem_Ici]; linarith) hx.2
        _ = (2 * T - (T + h * d')) * μ (2 * T) := by
            rw [intervalIntegral.integral_const, smul_eq_mul]
        _ ≤ 2 * h * μ (2 * T) := by gcongr
    linarith
  exact abs_le.2 ⟨by linarith, by linarith⟩
