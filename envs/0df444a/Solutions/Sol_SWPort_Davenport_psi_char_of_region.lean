-- Prove2me | solution 1 for SWPort.Davenport.psi_char_of_region
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T20:33:43.824979+00:00
-- url     : https://prove2.me/submissions/b4206d41-cfac-4f09-9ee0-3e101b8c4a99

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_SWPort_001
import Theorems.Thm_SWPort_Davenport_logDeriv_LFunction_region_bound
import Theorems.Thm_SWPort_Davenport_neg_logDeriv_LFunction_le_sum_zeros
import Theorems.Thm_SWPort_Davenport_perron_of_region_bound

section
-- module Solutions.Artin.SW.Thm.Davenport_LFunction_zero_one_sub_of_isQuadratic
namespace SWPort
/-! Ported from prove2.me: `Davenport.LFunction_zero_one_sub_of_isQuadratic` (64fb2bde-6d05-40d6-a9f1-4dd950241fc5, statement by alya); proof = accepted direct submission 921768ab-6536-4938-b7d9-e354d98ac4e9 by alya. -/















open Finset DirichletCharacter Vino

namespace SolAux

/-- The Euler-type correction factor relating `L(s, χ)` to `L(s, χ*)` is nonzero when
`0 < re s`, since each factor `1 - ψ p * p ^ (-s)` has `‖ψ p * p ^ (-s)‖ < 1`. -/
private lemma prod_factor_ne_zero {M : ℕ} (N : ℕ) (ψ : DirichletCharacter ℂ M) {s : ℂ}
    (hs : 0 < s.re) :
    ∏ p ∈ N.primeFactors, (1 - ψ p * (p : ℂ) ^ (-s)) ≠ 0 := by
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
  have hp0 : 0 < p := Nat.pos_of_mem_primeFactors hp
  have hnorm : ‖ψ (p : ZMod M) * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hp0]
    have hr : (0 : ℝ) ≤ (p : ℝ) ^ (-s).re :=
      (Real.rpow_pos_of_pos (by linarith) _).le
    have h1 : ‖ψ (p : ZMod M)‖ * (p : ℝ) ^ (-s).re ≤ 1 * (p : ℝ) ^ (-s).re :=
      mul_le_mul_of_nonneg_right (ψ.norm_le_one _) hr
    have h2 : (p : ℝ) ^ (-s).re < 1 := by
      refine Real.rpow_lt_one_of_one_lt_of_neg hp1 ?_
      simpa using hs
    calc ‖ψ (p : ZMod M)‖ * (p : ℝ) ^ (-s).re
        ≤ 1 * (p : ℝ) ^ (-s).re := h1
      _ = (p : ℝ) ^ (-s).re := one_mul _
      _ < 1 := h2
  intro hzero
  rw [sub_eq_zero] at hzero
  rw [← hzero, norm_one] at hnorm
  exact lt_irrefl _ hnorm

/-- The archimedean gamma factor is nonzero in the right half plane `0 < re s`. -/
private lemma gammaFactor_ne_zero {N : ℕ} (ψ : DirichletCharacter ℂ N) {s : ℂ} (hs : 0 < s.re) :
    ψ.gammaFactor s ≠ 0 := by
  rcases ψ.even_or_odd with hp | hp
  · rw [hp.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos hs
  · rw [hp.gammaFactor_def]
    refine Complex.Gammaℝ_ne_zero_of_re_pos ?_
    simp only [Complex.add_re, Complex.one_re]
    linarith

end SolAux

theorem _root_.SWPort.Davenport.LFunction_zero_one_sub_of_isQuadratic (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsQuadratic) (hχ1 : χ ≠ 1)
    (β : ℝ) (hβ₀ : 0 < β) (hβ₁ : β < 1)
    (h : DirichletCharacter.LFunction χ (β : ℂ) = 0) :
    DirichletCharacter.LFunction χ ((1 - β : ℝ) : ℂ) = 0 := by
  haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  set χ' : DirichletCharacter ℂ χ.conductor := χ.primitiveCharacter with hχ'def
  have hcl : changeLevel χ.conductor_dvd_level χ' = χ := χ.changeLevel_primitiveCharacter
  -- `χ'` is nontrivial
  have hχ'1 : χ' ≠ 1 := by
    intro hh
    exact hχ1 (by rw [← hcl, hh, map_one])
  -- `χ'` is quadratic
  have hχ'q : χ'.IsQuadratic := by
    rw [MulChar.isQuadratic_iff_sq_eq_one]
    refine (changeLevel_eq_one_iff χ.conductor_dvd_level).mp ?_
    rw [map_pow, hcl]
    exact hχ.sq_eq_one
  have hcond1 : χ.conductor ≠ 1 := fun hh => hχ1 (eq_one_iff_conductor_eq_one.mpr hh)
  have hreβ : (0 : ℝ) < ((β : ℂ)).re := by simpa using hβ₀
  have hre1β : (0 : ℝ) < (1 - (β : ℂ)).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith
  -- Step 2: `L(β, χ') = 0`
  have key1 : LFunction χ' (β : ℂ) = 0 := by
    have hstep := LFunction_changeLevel χ.conductor_dvd_level χ' (s := (β : ℂ)) (Or.inl hχ'1)
    rw [hcl, h] at hstep
    rcases mul_eq_zero.mp hstep.symm with h1 | h1
    · exact h1
    · exact absurd h1 (SolAux.prod_factor_ne_zero q χ' hreβ)
  -- Step 4: the completed L-function vanishes at `β`
  have hcomp : completedLFunction χ' (β : ℂ) = 0 := by
    have hstep := LFunction_eq_completed_div_gammaFactor χ' (β : ℂ) (Or.inr hcond1)
    rw [key1] at hstep
    exact (div_eq_zero_iff.mp hstep.symm).resolve_right (SolAux.gammaFactor_ne_zero χ' hreβ)
  -- Step 5: the functional equation
  have hfe := (χ.primitiveCharacter_isPrimitive).completedLFunction_one_sub (β : ℂ)
  rw [hχ'q.inv, hcomp, mul_zero] at hfe
  -- Step 6: back to the L-function of `χ`
  have key2 : LFunction χ' (1 - (β : ℂ)) = 0 := by
    rw [LFunction_eq_completed_div_gammaFactor χ' _ (Or.inr hcond1), hfe, zero_div]
  have hstep := LFunction_changeLevel χ.conductor_dvd_level χ' (s := 1 - (β : ℂ)) (Or.inl hχ'1)
  rw [hcl, key2, zero_mul] at hstep
  push_cast
  exact hstep

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.Davenport_neg_logDeriv_trivChar_le
namespace SWPort
/-! Ported from prove2.me: `Davenport.neg_logDeriv_trivChar_le` (efebc04c-2bb3-4ee8-9da2-2cd483b558df, statement by alya); proof = accepted direct submission 9c8aa629-da28-44a3-91a5-5c4c298cd65a by alya. -/






open Finset DirichletCharacter

open scoped LSeries.notation

namespace Sol

open ArithmeticFunction Complex

/-- Termwise comparison: for real `σ`, the `n`-th term of the `Λ`-series twisted by the trivial
character mod `q` has real part at most the `n`-th term of the plain `Λ`-series. -/
private lemma term_re_le (q : ℕ) (σ : ℝ) (n : ℕ) :
    (LSeries.term (↗(1 : DirichletCharacter ℂ q) * ↗Λ) (σ : ℂ) n).re
      ≤ (LSeries.term ↗Λ (σ : ℂ) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    have hcast : ((n : ℂ) ^ (σ : ℂ)) = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow (Nat.cast_nonneg n) σ]
      push_cast
      ring
    set A : ℝ := (Λ n) / ((n : ℝ) ^ σ) with hA
    have hA0 : 0 ≤ A := by
      exact div_nonneg vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) σ)
    have hdiv : ((Λ n : ℝ) : ℂ) / ((n : ℂ) ^ (σ : ℂ)) = (A : ℂ) := by
      rw [hcast, hA]
      push_cast
      ring
    have h1 : ((↗(1 : DirichletCharacter ℂ q) * ↗Λ) n) / ((n : ℂ) ^ (σ : ℂ))
        = (1 : DirichletCharacter ℂ q) (n : ZMod q) * (A : ℂ) := by
      simp only [Pi.mul_apply]
      rw [mul_div_assoc, hdiv]
    rw [h1, hdiv]
    have hre : ((1 : DirichletCharacter ℂ q) (n : ZMod q)).re ≤ 1 :=
      (Complex.re_le_norm _).trans (DirichletCharacter.norm_le_one _ _)
    have : (((1 : DirichletCharacter ℂ q) (n : ZMod q)) * (A : ℂ)).re
        = ((1 : DirichletCharacter ℂ q) (n : ZMod q)).re * A := by
      simp [Complex.mul_re]
    rw [this, Complex.ofReal_re]
    nlinarith

/-- The Dirichlet series of `χ₀ · Λ` at a real point `σ > 1` has real part at most that of the
Dirichlet series of `Λ`. -/
private lemma LSeries_twist_re_le (q : ℕ) (σ : ℝ) (hσ : 1 < σ) :
    (LSeries (↗(1 : DirichletCharacter ℂ q) * ↗Λ) (σ : ℂ)).re
      ≤ (LSeries ↗Λ (σ : ℂ)).re := by
  have hs : 1 < ((σ : ℂ)).re := by simpa using hσ
  have h1 : LSeriesSummable (↗(1 : DirichletCharacter ℂ q) * ↗Λ) (σ : ℂ) :=
    DirichletCharacter.LSeriesSummable_twist_vonMangoldt _ hs
  have h2 : LSeriesSummable ↗Λ (σ : ℂ) := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have h1' : Summable fun n : ℕ ↦
      (LSeries.term (↗(1 : DirichletCharacter ℂ q) * ↗Λ) (σ : ℂ) n).re :=
    ⟨_, Complex.hasSum_re h1.hasSum⟩
  have h2' : Summable fun n : ℕ ↦ (LSeries.term ↗Λ (σ : ℂ) n).re :=
    ⟨_, Complex.hasSum_re h2.hasSum⟩
  rw [LSeries, LSeries, Complex.re_tsum h1, Complex.re_tsum h2]
  exact h1'.tsum_le_tsum (fun n ↦ term_re_le q σ n) h2'

/-- `-ζ'/ζ(σ) - 1/(σ-1)` is bounded on `(1, 2]`. -/
private lemma zeta_bound : ∃ c : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
    (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + c := by
  have hK : IsCompact ((fun x : ℝ ↦ (x : ℂ)) '' Set.Icc (1 : ℝ) 2) :=
    isCompact_Icc.image Complex.continuous_ofReal
  have hzeta : DirichletCharacter.LFunctionTrivChar 1 = riemannZeta :=
    DirichletCharacter.LFunction_modOne_eq (χ := 1)
  have hsub : ((fun x : ℝ ↦ (x : ℂ)) '' Set.Icc (1 : ℝ) 2)
      ⊆ {s | s = 1 ∨ DirichletCharacter.LFunctionTrivChar 1 s ≠ 0} := by
    rintro _ ⟨x, hx, rfl⟩
    rcases eq_or_lt_of_le hx.1 with h | h
    · exact Or.inl (by rw [← h]; norm_num)
    · exact Or.inr (by rw [hzeta]; exact riemannZeta_ne_zero_of_one_lt_re (by simpa using h))
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn
    ((DirichletCharacter.continuousOn_neg_logDeriv_LFunctionTrivChar₁ 1).mono hsub)
  refine ⟨C, fun σ hσ1 hσ2 ↦ ?_⟩
  set s : ℂ := (σ : ℂ) with hsdef
  have hs1 : s ≠ 1 := by
    intro h
    rw [hsdef, Complex.ofReal_eq_one] at h
    exact absurd h (by linarith)
  have hsub1 : s - 1 ≠ 0 := sub_ne_zero_of_ne hs1
  have hz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re (by simpa [hsdef] using hσ1)
  have hF : DirichletCharacter.LFunctionTrivChar₁ 1 s = (s - 1) * riemannZeta s := by
    simp only [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hs1]
    rw [hzeta]
  have hdF : deriv (DirichletCharacter.LFunctionTrivChar₁ 1) s
      = (s - 1) * deriv riemannZeta s + riemannZeta s := by
    rw [DirichletCharacter.deriv_LFunctionTrivChar₁_apply_of_ne_one 1 hs1, hzeta]
  have hkey : -deriv riemannZeta s / riemannZeta s
      = (-deriv (DirichletCharacter.LFunctionTrivChar₁ 1) s
          / DirichletCharacter.LFunctionTrivChar₁ 1 s) + 1 / (s - 1) := by
    rw [hdF, hF]
    field_simp
    ring
  have h1re : ((1 : ℂ) / (s - 1)).re = 1 / (σ - 1) := by
    have hs' : s - 1 = ((σ - 1 : ℝ) : ℂ) := by rw [hsdef]; push_cast; ring
    rw [hs', show ((1 : ℂ) / (((σ - 1 : ℝ)) : ℂ)) = (((1 / (σ - 1) : ℝ)) : ℂ) by push_cast; ring]
    exact Complex.ofReal_re _
  have hbound := hC s ⟨σ, ⟨le_of_lt hσ1, hσ2⟩, rfl⟩
  have hre := (Complex.re_le_norm (-deriv (DirichletCharacter.LFunctionTrivChar₁ 1) s
      / DirichletCharacter.LFunctionTrivChar₁ 1 s)).trans hbound
  rw [hkey, Complex.add_re, h1re]
  linarith

end Sol

theorem _root_.SWPort.Davenport.neg_logDeriv_trivChar_le : ∃ c : ℝ, ∀ (q : ℕ) [NeZero q] (σ : ℝ), 1 < σ → σ ≤ 2 →
    (-(deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) (σ : ℂ)
        / DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) (σ : ℂ))).re
      ≤ 1 / (σ - 1) + c := by
  obtain ⟨c, hc⟩ := Sol.zeta_bound
  refine ⟨c, fun q _ σ hσ1 hσ2 ↦ ?_⟩
  have hs : 1 < ((σ : ℂ)).re := by simpa using hσ1
  have e1 : LSeries (↗(1 : DirichletCharacter ℂ q) * ↗ArithmeticFunction.vonMangoldt) (σ : ℂ)
      = -(deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) (σ : ℂ)
          / DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) (σ : ℂ)) := by
    rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq _ hs, neg_div,
      ← DirichletCharacter.deriv_LFunction_eq_deriv_LSeries _ hs,
      ← DirichletCharacter.LFunction_eq_LSeries _ hs]
  have e2 : LSeries ↗ArithmeticFunction.vonMangoldt (σ : ℂ)
      = -deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ) :=
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs
  rw [← e1]
  refine le_trans (Sol.LSeries_twist_re_le q σ hσ1) ?_
  rw [e2]
  exact hc σ hσ1 hσ2

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.Davenport_real_zero_multiple_le
namespace SWPort
/-! Ported from prove2.me: `Davenport.real_zero_multiple_le` (6b7dd420-f903-43c3-9366-7cfc3f841af1, statement by alya); proof = accepted sketch submission fb50a9ad-288e-45fd-b09b-1e94b153e738 by alya. -/












/-!
# A multiple real zero of `L(s, χ)` is far from `1` (Davenport §14)

If `β ∈ (0,1)` is a zero of order `≥ 2` of `L(·, χ)`, `χ ≠ 1 mod q`, then `β ≤ 1 - c / log (2q)`.

Proof: with `σ = 1 + δ / log (2q)` and the multiset `Z = {β, β}`, the zero-sum bound
`Davenport.neg_logDeriv_LFunction_le_sum_zeros` gives
`-Re L'/L(σ, χ) ≤ c_Z log (2q) - 2/(σ - β)`, while the trivial comparison
`-Re L'/L(σ, χ) ≥ ζ'/ζ(σ) ≥ -1/(σ - 1) - c₀` (from `Davenport.neg_logDeriv_trivChar_le` with
`q = 1`) bounds the same quantity from below; solving for `σ - β` gives the claim.
-/

open Complex

namespace DavenportRZ

/-- The trivial lower bound `-Re L'/L(σ, χ) ≥ -(-ζ'/ζ(σ))` for real `σ > 1`. -/
private lemma neg_logDeriv_ge {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : 1 < σ) :
    -(-(deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ))).re
      ≤ (-(deriv (DirichletCharacter.LFunction χ) (σ : ℂ)
          / DirichletCharacter.LFunction χ (σ : ℂ))).re := by
  have hs : 1 < ((σ : ℂ)).re := by simpa using hσ
  -- express both sides as Dirichlet series
  have h1 : -(deriv (DirichletCharacter.LFunction χ) (σ : ℂ)
      / DirichletCharacter.LFunction χ (σ : ℂ))
      = LSeries (fun n : ℕ => (χ n : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) := by
    rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
      DirichletCharacter.LFunction_eq_LSeries χ hs, ← neg_div]
    exact (DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs).symm
  have h2 : -(deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ))
      = LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) := by
    rw [← neg_div]
    exact (ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs).symm
  rw [h1, h2]
  have hsumχ : LSeriesSummable (fun n : ℕ => (χ n : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ))
      (σ : ℂ) := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs
  have hsumΛ : LSeriesSummable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  unfold LSeries
  rw [Complex.re_tsum hsumχ, Complex.re_tsum hsumΛ, ← tsum_neg]
  have hΛre : Summable (fun n => (LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ))
      (σ : ℂ) n).re) := Complex.reCLM.summable hsumΛ
  have hχre : Summable (fun n => (LSeries.term
      (fun n : ℕ => (χ n : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) n).re) :=
    Complex.reCLM.summable hsumχ
  refine Summable.tsum_le_tsum (fun n => ?_) hΛre.neg hχre
  -- termwise comparison
  have hn : ‖LSeries.term (fun n : ℕ => (χ n : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) n‖
      ≤ ‖LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) n‖ := by
    refine LSeries.norm_term_le _ ?_
    rw [norm_mul]
    have := DirichletCharacter.norm_le_one χ (n : ZMod q)
    have h0 : 0 ≤ ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖ := norm_nonneg _
    nlinarith
  have hre : (LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) n).re
      = ‖LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) n‖ := by
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [LSeries.term_zero]
    · have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn0
      have e1 : ‖LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) n‖
          = ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ := by
        rw [LSeries.norm_term_eq, if_neg hn0, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, Complex.ofReal_re]
      have e2 : (LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) n).re
          = ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ σ := by
        rw [LSeries.term_of_ne_zero hn0, show (n : ℂ) = ((n : ℝ) : ℂ) by simp,
          ← Complex.ofReal_cpow hpos.le, ← Complex.ofReal_div, Complex.ofReal_re]
      rw [e1, e2]
  have := Complex.abs_re_le_norm
    (LSeries.term (fun n : ℕ => (χ n : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ)) (σ : ℂ) n)
  have := (abs_le.mp this).1
  linarith

private lemma log_two_pos' : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)

private lemma log_two_le_log_2q (q : ℕ) [NeZero q] : Real.log 2 ≤ Real.log (2 * q) := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  exact Real.log_le_log (by norm_num) (by linarith)

end DavenportRZ

open DavenportRZ in
theorem _root_.SWPort.Davenport.real_zero_multiple_le :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
        ∀ β : ℝ, 0 < β → β < 1 →
          2 ≤ analyticOrderNatAt (DirichletCharacter.LFunction χ) (β : ℂ) →
            β ≤ 1 - c / Real.log (2 * q) := by
  obtain ⟨cZ, hcZ, HZ⟩ := Davenport.neg_logDeriv_LFunction_le_sum_zeros
  obtain ⟨c₀, H₀⟩ := Davenport.neg_logDeriv_trivChar_le
  have hl2 : (0 : ℝ) < Real.log 2 := log_two_pos'
  set c₀' : ℝ := max c₀ 0 with hc₀'
  have hc₀'0 : 0 ≤ c₀' := le_max_right _ _
  set K' : ℝ := c₀' / Real.log 2 + cZ with hK'
  have hK'pos : 0 < K' := by positivity
  set δ : ℝ := min (Real.log 2 / 8) (1 / (2 * K')) with hδ
  have hδpos : 0 < δ := lt_min (by positivity) (by positivity)
  have hδ1 : δ ≤ Real.log 2 / 8 := min_le_left _ _
  have hδ2 : δ ≤ 1 / (2 * K') := min_le_right _ _
  have hδK : δ * K' ≤ 1 / 2 := by
    rw [le_div_iff₀ (by positivity)] at hδ2
    linarith
  refine ⟨δ / 3, by positivity, ?_⟩
  intro q _ χ hχ β hβ0 hβ1 hord
  set L : ℝ := Real.log (2 * q) with hL
  have hL2 : Real.log 2 ≤ L := log_two_le_log_2q q
  have hLpos : 0 < L := lt_of_lt_of_le hl2 hL2
  -- the order of the zero at `β` is at least two (as an extended natural number)
  have hord' : (2 : ℕ∞) ≤ analyticOrderAt (DirichletCharacter.LFunction χ) (β : ℂ) := by
    have hne : analyticOrderAt (DirichletCharacter.LFunction χ) (β : ℂ) ≠ ⊤ := by
      intro htop
      have : analyticOrderNatAt (DirichletCharacter.LFunction χ) (β : ℂ) = 0 := by
        rw [analyticOrderNatAt, htop]; rfl
      omega
    rw [← ENat.coe_toNat hne]
    exact_mod_cast hord
  by_cases hcase : β < 1 / 2 + δ / L
  · -- `β` is far from `1` for trivial reasons
    have h1 : (δ / 3 + δ) / L ≤ 1 / 2 := by
      rw [div_le_iff₀ hLpos]
      have : δ / 3 + δ ≤ Real.log 2 / 2 := by linarith
      linarith
    have h2 : δ / 3 / L + δ / L = (δ / 3 + δ) / L := by ring
    linarith
  · push Not at hcase
    set σ : ℝ := 1 + δ / L with hσ
    have hσ1 : 1 < σ := by
      have : 0 < δ / L := by positivity
      linarith
    have hσ2 : σ ≤ 2 := by
      have : δ / L ≤ δ / Real.log 2 := div_le_div_of_nonneg_left hδpos.le hl2 hL2
      have : δ / Real.log 2 ≤ 1 / 8 := by
        rw [div_le_iff₀ hl2]; linarith
      linarith
    have hσβ : 0 < σ - β := by linarith
    have hσβ' : σ - β ≤ 1 / 2 := by linarith
    -- apply the zero-sum bound with `Z = {β, β}`
    have hs1 : 1 < ((σ : ℂ)).re := by simpa using hσ1
    have hs2 : ((σ : ℂ)).re ≤ 2 := by simpa using hσ2
    set Z : Multiset ℂ := {(β : ℂ), (β : ℂ)} with hZ
    have hZmem : ∀ ρ ∈ Z, ‖ρ - (σ : ℂ)‖ ≤ 1 / 2 := by
      intro ρ hρ
      have : ρ = (β : ℂ) := by
        simp only [hZ, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hρ
        rcases hρ with h | h <;> exact h
      rw [this, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm,
        abs_of_pos hσβ]
      exact hσβ'
    have hZcount : ∀ ρ : ℂ, (Z.count ρ : ℕ∞) ≤ analyticOrderAt (DirichletCharacter.LFunction χ) ρ := by
      intro ρ
      by_cases hρ : ρ = (β : ℂ)
      · subst hρ
        have : Z.count (β : ℂ) = 2 := by
          simp [hZ, Multiset.insert_eq_cons]
        rw [this]
        exact hord'
      · have : Z.count ρ = 0 := by
          simp [hZ, Multiset.insert_eq_cons, hρ]
        rw [this]
        simp
    have hupper := HZ q χ hχ (σ : ℂ) hs1 hs2 Z hZmem hZcount
    have hsum : (Z.map fun ρ => (1 / ((σ : ℂ) - ρ)).re).sum = 2 / (σ - β) := by
      simp only [hZ, Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
        Multiset.sum_cons, Multiset.sum_singleton]
      rw [← Complex.ofReal_sub, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
      ring
    rw [hsum] at hupper
    have him : |((σ : ℂ)).im| = 0 := by simp
    rw [him] at hupper
    have hlog : Real.log ((q : ℝ) * (0 + 2)) = L := by
      rw [hL]; congr 1; ring
    rw [hlog] at hupper
    -- the lower bound
    have hlower := neg_logDeriv_ge χ hσ1
    have htriv := H₀ 1 σ hσ1 hσ2
    have hzeta : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) = riemannZeta :=
      DirichletCharacter.LFunction_modOne_eq
    rw [hzeta] at htriv
    have hσm1 : σ - 1 = δ / L := by rw [hσ]; ring
    rw [hσm1] at htriv
    have hc₀le : c₀ ≤ c₀' := le_max_left _ _
    -- combine: `2/(σ-β) ≤ L/δ + c₀' + cZ L ≤ L (1/δ + K')`
    have hcomb : 2 / (σ - β) ≤ L / δ + c₀' + cZ * L := by
      have : 1 / (δ / L) = L / δ := by rw [one_div_div]
      linarith
    have hc₀L : c₀' ≤ c₀' / Real.log 2 * L := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
      exact mul_le_mul_of_nonneg_left hL2 hc₀'0
    have hcomb2 : 2 / (σ - β) ≤ L * (1 / δ + K') := by
      rw [hK']
      have : L / δ = L * (1 / δ) := by ring
      linarith
    -- hence `σ - β ≥ 2 / (L (1/δ + K')) ≥ 4δ / (3L)`
    have hpos2 : 0 < L * (1 / δ + K') := by positivity
    have hgap : 2 / (L * (1 / δ + K')) ≤ σ - β := by
      rw [div_le_iff₀ hpos2]
      rw [div_le_iff₀ hσβ] at hcomb2
      linarith
    have hgap2 : 4 * δ / (3 * L) ≤ 2 / (L * (1 / δ + K')) := by
      rw [div_le_div_iff₀ (by positivity) hpos2]
      have h32 : 1 + δ * K' ≤ 3 / 2 := by linarith
      calc 4 * δ * (L * (1 / δ + K')) = 4 * L * (1 + δ * K') := by field_simp
        _ ≤ 4 * L * (3 / 2) := by gcongr
        _ = 2 * (3 * L) := by ring
    have : δ / 3 / L = 4 * δ / (3 * L) - δ / L := by field_simp; ring
    linarith

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.Davenport_psi_char_of_region
namespace SWPort
/-! Ported from prove2.me: `Davenport.psi_char_of_region` (0b61efc4-9fee-4960-8136-bdc620a7c947, statement by alya); proof = accepted sketch submission 80a16960-3bff-41fb-a6ef-fe2ab804c25d by alya. -/






















open Finset DirichletCharacter Vino Davenport

namespace SolPsiCharOfRegion

/-- The analytic order of `L(·, χ)` at a zero is at least `1`, for `χ ≠ 1`. -/
private lemma one_le_order {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {z : ℂ}
    (hz : DirichletCharacter.LFunction χ z = 0) :
    1 ≤ analyticOrderNatAt (DirichletCharacter.LFunction χ) z := by
  have hdiff : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
    DirichletCharacter.differentiable_LFunction hχ
  have hanNhd : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) Set.univ :=
    hdiff.differentiableOn.analyticOnNhd isOpen_univ
  have han : AnalyticAt ℂ (DirichletCharacter.LFunction χ) z := hanNhd z (Set.mem_univ z)
  have hne0 : analyticOrderAt (DirichletCharacter.LFunction χ) z ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨han, hz⟩
  have hnetop : analyticOrderAt (DirichletCharacter.LFunction χ) z ≠ ⊤ := by
    intro htop
    have hev : DirichletCharacter.LFunction χ =ᶠ[nhds z] 0 := analyticOrderAt_eq_top.mp htop
    have hzero := hanNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ z) hev
    have h2 : DirichletCharacter.LFunction χ 2 = 0 := hzero (Set.mem_univ 2)
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num) h2
  have hcast := Nat.cast_analyticOrderNatAt hnetop
  rcases Nat.eq_zero_or_pos (analyticOrderNatAt (DirichletCharacter.LFunction χ) z) with h0 | hpos
  · rw [h0] at hcast
    exact absurd hcast.symm hne0
  · exact hpos

/-- `log (q (|t| + 2)) > 0` when `1 ≤ q`. -/
private lemma log_region_pos {q : ℕ} (hq : (1:ℝ) ≤ (q:ℝ)) (s : ℂ) :
    0 < Real.log ((q : ℝ) * (|s.im| + 2)) := by
  apply Real.log_pos
  nlinarith [abs_nonneg s.im]

private lemma inRegion_mono {q : ℕ} (hq : (1:ℝ) ≤ (q:ℝ)) {c : ℝ} (hc : 0 < c) {s : ℂ}
    (h : InRegion (c/4) q s) : InRegion c q s := by
  have hlog := log_region_pos hq s
  unfold InRegion regionBoundary at h ⊢
  have : c / 4 / Real.log ((q:ℝ) * (|s.im| + 2)) ≤ c / Real.log ((q:ℝ) * (|s.im| + 2)) := by
    gcongr
    linarith
  linarith

/-- Every element of an exceptional set has real part at least `1/2`. -/
private lemma half_le_re {q : ℕ} [NeZero q] {c : ℝ} {χ : DirichletCharacter ℂ q} {E : Set ℂ}
    (hE : IsExceptionalSet c χ E) {z : ℂ} (hz : z ∈ E) : 1 / 2 ≤ z.re := by
  obtain ⟨him, hre0, hre1, hreg, hL, hquad, hχ1⟩ := hE.2.1 z hz
  by_contra hlt
  rw [not_le] at hlt
  have hzeq : ((z.re : ℝ) : ℂ) = z := by
    apply Complex.ext <;> simp [him]
  have hL' : DirichletCharacter.LFunction χ ((z.re : ℝ) : ℂ) = 0 := by rw [hzeq]; exact hL
  have hzero := Davenport.LFunction_zero_one_sub_of_isQuadratic q χ hquad hχ1 z.re hre0 hre1 hL'
  set s : ℂ := ((1 - z.re : ℝ) : ℂ) with hsdef
  have hs_re : s.re = 1 - z.re := by simp [hsdef]
  have hs_im : s.im = 0 := by simp [hsdef]
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hs_re
    simp only [Complex.one_re] at hs_re
    linarith
  have hreg' : InRegion c q s := by
    unfold InRegion regionBoundary at hreg ⊢
    rw [hs_im, hs_re]
    rw [him] at hreg
    linarith
  have hsE : s ∉ E := by
    intro hmem
    have heq : s = z := hE.1 hmem hz
    have hh : (1 : ℝ) - z.re = z.re := by rw [← hs_re, heq]
    linarith
  exact hE.2.2 s hs1 hreg' hsE hzero

end SolPsiCharOfRegion

open SolPsiCharOfRegion

set_option maxHeartbeats 1000000 in
open Classical in
theorem _root_.SWPort.Davenport.psi_char_of_region_oai (c : ℝ) (hc : 0 < c) :
    ∃ c₁ c₂ C : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (E : Set ℂ),
        IsExceptionalSet c χ E →
        ∀ N : ℕ, 2 ≤ N → (q : ℝ) ≤ Real.exp (c₂ * Real.sqrt (Real.log N)) →
          ‖vmSumChar q χ N - (if χ = 1 then (N : ℂ) else 0)
              + ∑ᶠ z ∈ E, (N : ℂ) ^ z / z‖
            ≤ C * N * Real.exp (-c₁ * Real.sqrt (Real.log N)) := by
  obtain ⟨C₂, hC₂pos, hC₂⟩ := Davenport.logDeriv_LFunction_region_bound c hc
  obtain ⟨c', hc'pos, hc'⟩ := Davenport.real_zero_multiple_le
  obtain ⟨c₁, c₂, C, hc₁, hc₂, hC, hPerron⟩ :=
    Davenport.perron_of_region_bound (c / 4) (C₂ + 2) (by positivity) (by positivity)
  set κ : ℝ := c' / (1 + c₂) with hκdef
  have hκpos : 0 < κ := by rw [hκdef]; positivity
  refine ⟨min c₁ (κ / 2), c₂, C + 4 * C₂ * (1 + c₂) / κ, lt_min hc₁ (by positivity), hc₂,
    by positivity, ?_⟩
  intro q _ χ E hE N hN2 hqN
  -- basic numerics
  set x : ℝ := Real.sqrt (Real.log N) with hxdef
  have hq1 : (1:ℝ) ≤ (q:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqpos : (0:ℝ) < (q:ℝ) := by linarith
  have hNr2 : (2:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN2
  have hNpos : (0:ℝ) < (N:ℝ) := by linarith
  have hNnat : 0 < N := by omega
  have hlog2N : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) hNr2
  have hlogNpos : 0 < Real.log N := lt_of_lt_of_le (Real.log_pos (by norm_num)) hlog2N
  have hx2 : x ^ 2 = Real.log N := Real.sq_sqrt hlogNpos.le
  have hxpos : 0 < x := Real.sqrt_pos.mpr hlogNpos
  have hlog2x : Real.log 2 ≤ x := by
    nlinarith [Real.log_two_lt_d9, Real.log_two_gt_d9, hx2, hxpos, hlog2N]
  set L2q : ℝ := Real.log (2 * q) with hL2qdef
  have hL2qpos : 0 < L2q := Real.log_pos (by linarith)
  have hlogq : Real.log q ≤ c₂ * x := by
    have := Real.log_le_log hqpos hqN
    rwa [Real.log_exp] at this
  have hL2qle : L2q ≤ (1 + c₂) * x := by
    have : L2q = Real.log 2 + Real.log q := by
      rw [hL2qdef, Real.log_mul (by norm_num) (by positivity)]
    rw [this]
    nlinarith
  -- the exceptional set as a finset
  have hEfin : E.Finite := hE.1.finite
  set Efin : Finset ℂ := hEfin.toFinset with hEfindef
  have hmemE : ∀ z : ℂ, z ∈ Efin ↔ z ∈ E := fun z => hEfin.mem_toFinset
  have hcard : Efin.card ≤ 1 :=
    Finset.card_le_one.mpr fun a ha b hb => hE.1 ((hmemE a).mp ha) ((hmemE b).mp hb)
  have hone : (1:ℂ) ∉ Efin := by
    intro h
    have h1 := (hE.2.1 1 ((hmemE 1).mp h)).2.2.1
    simp only [Complex.one_re] at h1
    linarith
  -- the data fed to the Perron theorem
  set a : ℕ → ℂ := fun n => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * χ (n : ZMod q)
    with hadef
  set G : ℂ → ℂ := fun s => -(deriv (DirichletCharacter.LFunction χ) s /
    DirichletCharacter.LFunction χ s) with hGdef
  set P : Finset ℂ := insert 1 Efin with hPdef
  set r : ℂ → ℂ := fun p => if p = 1 then (if χ = 1 then 1 else 0)
    else -(analyticOrderNatAt (DirichletCharacter.LFunction χ) p : ℂ) with hrdef
  have hrE : ∀ z ∈ Efin, r z = -(analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) := by
    intro z hz
    rw [hrdef]
    simp only [if_neg (fun h : z = 1 => hone (h ▸ hz))]
  have hr1 : r 1 = (if χ = 1 then (1:ℂ) else 0) := by rw [hrdef]; simp
  -- (a)
  have ha : ∀ n : ℕ, ‖a n‖ ≤ ArithmeticFunction.vonMangoldt n := by
    intro n
    rw [hadef]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    nlinarith [DirichletCharacter.norm_le_one χ (n : ZMod q), norm_nonneg (χ (n : ZMod q)),
      ArithmeticFunction.vonMangoldt_nonneg (n := n)]
  -- (b)
  have hGser : ∀ s : ℂ, 1 < s.re → G s = LSeries a s := by
    intro s hs
    have h1 : DirichletCharacter.LFunction χ s = LSeries (fun n : ℕ => (χ n : ℂ)) s :=
      DirichletCharacter.LFunction_eq_LSeries χ hs
    have h2 : deriv (DirichletCharacter.LFunction χ) s
        = deriv (LSeries (fun n : ℕ => (χ n : ℂ))) s :=
      DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs
    have h3 := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
    have h4 : LSeries a s
        = LSeries ((fun n : ℕ => (χ n : ℂ)) *
            (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ))) s := by
      refine LSeries_congr ?_ s
      intro n _
      rw [hadef]
      simp only [Pi.mul_apply]
      ring
    rw [hGdef]
    simp only
    rw [h1, h2, h4, h3]
    ring
  -- (c)
  have hana : AnalyticOnNhd ℂ G ({s : ℂ | InRegion (c / 4) q s ∧ 3 / 4 ≤ s.re} \ ↑P) := by
    rintro s ⟨⟨hreg, hre⟩, hsP⟩
    have hs1 : s ≠ 1 := by
      intro h
      exact hsP (by rw [h]; exact_mod_cast Finset.mem_insert_self (1:ℂ) Efin)
    have hLana : AnalyticAt ℂ (DirichletCharacter.LFunction χ) s := by
      refine DifferentiableOn.analyticAt (s := {z : ℂ | z ≠ 1}) (fun z hz => ?_)
        (isOpen_ne.mem_nhds hs1)
      exact (DirichletCharacter.differentiableAt_LFunction χ z (Or.inl hz)).differentiableWithinAt
    have hLne : DirichletCharacter.LFunction χ s ≠ 0 := by
      refine hE.2.2 s hs1 (inRegion_mono hq1 hc hreg) (fun hmem => hsP ?_)
      exact_mod_cast Finset.mem_insert_of_mem ((hmemE s).mpr hmem)
    exact (hLana.deriv.div hLana hLne).neg
  -- (d)
  have hPre : ∀ p ∈ P, 1 / 2 ≤ p.re ∧ p.re ≤ 1 := by
    intro p hp
    rw [hPdef, Finset.mem_insert] at hp
    rcases hp with rfl | hp
    · norm_num
    · have hpE := (hmemE p).mp hp
      exact ⟨half_le_re hE hpE, le_of_lt (hE.2.1 p hpE).2.2.1⟩
  -- (e)
  have hrsum : (∑ p ∈ P, ‖r p‖) ≤ (C₂ + 2) * L2q := by
    have hlog2L : Real.log 2 ≤ L2q := by
      rw [hL2qdef]
      exact Real.log_le_log (by norm_num) (by linarith)
    have hb1 : ‖r 1‖ ≤ 1 := by rw [hr1]; split_ifs <;> simp
    have hb2 : ∑ z ∈ Efin, ‖r z‖ ≤ C₂ * L2q := by
      have hterm : ∀ z ∈ Efin, ‖r z‖ ≤ C₂ * L2q := by
        intro z hz
        rw [hrE z hz, norm_neg, Complex.norm_natCast]
        exact (hC₂ q χ E hE).1 z ((hmemE z).mp hz)
      calc ∑ z ∈ Efin, ‖r z‖ ≤ Efin.card • (C₂ * L2q) :=
            Finset.sum_le_card_nsmul _ _ _ hterm
        _ ≤ C₂ * L2q := by
            rw [nsmul_eq_mul]
            have : (Efin.card : ℝ) ≤ 1 := by exact_mod_cast hcard
            nlinarith [mul_pos hC₂pos hL2qpos]
    rw [hPdef, Finset.sum_insert hone]
    nlinarith [Real.log_two_gt_d9]
  -- (f)
  have hGbd : ∀ s : ℂ, InRegion (c / 4) q s → 3 / 4 ≤ s.re → s ∉ P →
      ‖G s - ∑ p ∈ P, r p / (s - p)‖ ≤ (C₂ + 2) * Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2 := by
    intro s hreg hre hsP
    have hs1 : s ≠ 1 := by
      intro h
      exact hsP (by rw [hPdef, h]; exact Finset.mem_insert_self (1:ℂ) Efin)
    have hsE : s ∉ E := fun hmem =>
      hsP (by rw [hPdef]; exact Finset.mem_insert_of_mem ((hmemE s).mpr hmem))
    have hb := (hC₂ q χ E hE).2 s hreg hre hs1 hsE
    rw [finsum_mem_eq_finite_toFinset_sum _ hEfin] at hb
    have hkey : G s - ∑ p ∈ P, r p / (s - p) =
        -(deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s
          + (if χ = 1 then 1 / (s - 1) else 0)
          - ∑ z ∈ Efin,
              (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) / (s - z)) := by
      rw [hPdef, Finset.sum_insert hone, hr1]
      have hcongr : ∀ z ∈ Efin, r z / (s - z)
          = -((analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) / (s - z)) := by
        intro z hz
        rw [hrE z hz]
        ring
      rw [Finset.sum_congr rfl hcongr, Finset.sum_neg_distrib, hGdef]
      simp only
      split_ifs <;> ring
    rw [hkey, norm_neg]
    have hsq : (0:ℝ) ≤ Real.log ((q : ℝ) * (|s.im| + 2)) ^ 2 := sq_nonneg _
    nlinarith
  -- apply Perron
  have key := hPerron q a G P r ha hGser hana hPre hrsum hGbd N hN2 hqN
  have hsum_a : (∑ n ∈ Finset.range N, a n) = vmSumChar q χ N := rfl
  have hsum_r : ∑ p ∈ P, r p * (N : ℂ) ^ p / p
      = (if χ = 1 then (N : ℂ) else 0)
        - ∑ z ∈ Efin, (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ)
            * (N : ℂ) ^ z / z := by
    rw [hPdef, Finset.sum_insert hone, hr1]
    have hcongr : ∀ z ∈ Efin, r z * (N : ℂ) ^ z / z
        = -((analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) * (N : ℂ) ^ z / z) := by
      intro z hz
      rw [hrE z hz]
      ring
    rw [Finset.sum_congr rfl hcongr, Finset.sum_neg_distrib, Complex.cpow_one]
    split_ifs <;> ring
  rw [hsum_a, hsum_r] at key
  rw [finsum_mem_eq_finite_toFinset_sum _ hEfin]
  -- the difference between the two shapes
  have hdiffsum : ∑ z ∈ Efin,
      ((analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) - 1) * (N : ℂ) ^ z / z
      = (∑ z ∈ Efin, (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ)
            * (N : ℂ) ^ z / z) - ∑ z ∈ Efin, (N : ℂ) ^ z / z := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun z _ => by ring)
  have hdecomp : vmSumChar q χ N - (if χ = 1 then (N : ℂ) else 0) + ∑ z ∈ Efin, (N : ℂ) ^ z / z
      = (vmSumChar q χ N - ((if χ = 1 then (N : ℂ) else 0)
          - ∑ z ∈ Efin, (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ)
              * (N : ℂ) ^ z / z))
        - ∑ z ∈ Efin,
            ((analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) - 1) * (N : ℂ) ^ z / z := by
    rw [hdiffsum]
    ring
  -- bound on the correction sum
  have hcorr : ‖∑ z ∈ Efin,
      ((analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) - 1) * (N : ℂ) ^ z / z‖
      ≤ 4 * C₂ * (1 + c₂) / κ * N * Real.exp (-(κ / 2) * x) := by
    have hKpos : (0:ℝ) < 4 * C₂ * (1 + c₂) / κ := by positivity
    have hRHS : (0:ℝ) ≤ 4 * C₂ * (1 + c₂) / κ * N * Real.exp (-(κ / 2) * x) := by positivity
    have hxexp : x ≤ 2 / κ * Real.exp (κ * x / 2) := by
      have h1 : κ * x / 2 ≤ Real.exp (κ * x / 2) := by
        have := Real.add_one_le_exp (κ * x / 2); linarith
      have h2 : x = 2 / κ * (κ * x / 2) := by field_simp
      calc x = 2 / κ * (κ * x / 2) := h2
        _ ≤ 2 / κ * Real.exp (κ * x / 2) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
    have hexpprod : Real.exp (κ * x / 2) * Real.exp (-(κ * x)) = Real.exp (-(κ / 2) * x) := by
      rw [← Real.exp_add]; congr 1; ring
    have hterm : ∀ z ∈ Efin,
        ‖((analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) - 1) * (N : ℂ) ^ z / z‖
          ≤ 4 * C₂ * (1 + c₂) / κ * N * Real.exp (-(κ / 2) * x) := by
      intro z hz
      have hzE : z ∈ E := (hmemE z).mp hz
      obtain ⟨him, hre0, hre1, hreg, hL, hquad, hχ1⟩ := hE.2.1 z hzE
      have hhalf : (1:ℝ) / 2 ≤ z.re := half_le_re hE hzE
      have hm1 : 1 ≤ analyticOrderNatAt (DirichletCharacter.LFunction χ) z :=
        one_le_order hχ1 hL
      have hmC : (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℝ) ≤ C₂ * L2q :=
        (hC₂ q χ E hE).1 z hzE
      rcases eq_or_lt_of_le hm1 with hm_eq | hm_lt
      · rw [← hm_eq]
        simpa using hRHS
      · have hm2 : 2 ≤ analyticOrderNatAt (DirichletCharacter.LFunction χ) z := hm_lt
        have hzeq : ((z.re : ℝ) : ℂ) = z := by
          apply Complex.ext <;> simp [him]
        have hm2' : 2 ≤ analyticOrderNatAt (DirichletCharacter.LFunction χ) ((z.re : ℝ) : ℂ) := by
          rw [hzeq]; exact hm2
        have hbeta : z.re ≤ 1 - c' / L2q := by
          have := hc' q χ hχ1 z.re hre0 hre1 hm2'
          rwa [← hL2qdef] at this
        have hzn : (1:ℝ) / 2 ≤ ‖z‖ :=
          le_trans hhalf (le_trans (le_abs_self z.re) (Complex.abs_re_le_norm z))
        have hznpos : (0:ℝ) < ‖z‖ := by linarith
        -- bound the coefficient
        have hnormnum :
            ‖((analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) - 1)‖ ≤ C₂ * L2q := by
          have hc1 : ((analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) - 1)
              = (((analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℝ) - 1 : ℝ) : ℂ) := by
            push_cast; ring
          have hnn : (0:ℝ) ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℝ) - 1 := by
            have : (1:ℝ) ≤ (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℝ) := by
              exact_mod_cast hm1
            linarith
          rw [hc1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
          linarith
        -- bound the power
        have hcpow : ‖(N : ℂ) ^ z‖ = (N : ℝ) ^ z.re :=
          Complex.norm_natCast_cpow_of_pos hNnat z
        have hc'L : κ / x ≤ c' / L2q := by
          have h1 : κ / x = c' / ((1 + c₂) * x) := by
            rw [hκdef]; field_simp
          rw [h1]
          gcongr
        have hzre : z.re ≤ 1 - κ / x := by linarith
        have hrpow : (N : ℝ) ^ z.re ≤ (N : ℝ) * Real.exp (-(κ * x)) := by
          rw [Real.rpow_def_of_pos hNpos]
          have hstep : Real.log N * z.re ≤ Real.log N * (1 - κ / x) :=
            mul_le_mul_of_nonneg_left hzre hlogNpos.le
          have heq : Real.log N * (1 - κ / x) = Real.log N + -(κ * x) := by
            have hxne : x ≠ 0 := ne_of_gt hxpos
            rw [← hx2]; field_simp; ring
          calc Real.exp (Real.log N * z.re)
              ≤ Real.exp (Real.log N + -(κ * x)) := by
                apply Real.exp_le_exp.mpr; linarith [heq ▸ hstep]
            _ = (N : ℝ) * Real.exp (-(κ * x)) := by
                rw [Real.exp_add, Real.exp_log hNpos]
        -- put the pieces together
        have hnormexpand :
            ‖((analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) - 1)
                * (N : ℂ) ^ z / z‖
              = ‖((analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) - 1)‖
                  * (N : ℝ) ^ z.re / ‖z‖ := by
          rw [norm_div, norm_mul, hcpow]
        rw [hnormexpand]
        have hEnn : (0:ℝ) ≤ (N : ℝ) * Real.exp (-(κ * x)) := by positivity
        have hBnn : (0:ℝ) ≤ C₂ * L2q * ((N : ℝ) * Real.exp (-(κ * x))) := by positivity
        have hnum :
            ‖((analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) - 1)‖
                * (N : ℝ) ^ z.re
              ≤ C₂ * L2q * ((N : ℝ) * Real.exp (-(κ * x))) :=
          mul_le_mul hnormnum hrpow (Real.rpow_nonneg hNpos.le _) (by positivity)
        have hstep1 :
            ‖((analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) - 1)‖
                * (N : ℝ) ^ z.re / ‖z‖
              ≤ 2 * (C₂ * L2q * ((N : ℝ) * Real.exp (-(κ * x)))) := by
          rw [div_le_iff₀ hznpos]
          nlinarith [mul_nonneg hBnn (by linarith : (0:ℝ) ≤ 2 * ‖z‖ - 1)]
        refine le_trans hstep1 ?_
        have hA : C₂ * L2q ≤ C₂ * ((1 + c₂) * x) :=
          mul_le_mul_of_nonneg_left hL2qle hC₂pos.le
        have hB : C₂ * ((1 + c₂) * x)
            ≤ C₂ * ((1 + c₂) * (2 / κ * Real.exp (κ * x / 2))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hxexp (by positivity)) hC₂pos.le
        calc 2 * (C₂ * L2q * ((N : ℝ) * Real.exp (-(κ * x))))
            ≤ 2 * (C₂ * ((1 + c₂) * (2 / κ * Real.exp (κ * x / 2)))
                * ((N : ℝ) * Real.exp (-(κ * x)))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right (le_trans hA hB) hEnn) (by norm_num)
          _ = 4 * C₂ * (1 + c₂) / κ * N * Real.exp (-(κ / 2) * x) := by
              rw [← hexpprod]; field_simp; ring
    calc ‖∑ z ∈ Efin,
          ((analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) - 1) * (N : ℂ) ^ z / z‖
        ≤ ∑ z ∈ Efin,
            ‖((analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) - 1)
              * (N : ℂ) ^ z / z‖ := norm_sum_le _ _
      _ ≤ Efin.card • (4 * C₂ * (1 + c₂) / κ * N * Real.exp (-(κ / 2) * x)) :=
          Finset.sum_le_card_nsmul _ _ _ hterm
      _ ≤ 4 * C₂ * (1 + c₂) / κ * N * Real.exp (-(κ / 2) * x) := by
          rw [nsmul_eq_mul]
          have hcr : (Efin.card : ℝ) ≤ 1 := by exact_mod_cast hcard
          nlinarith
  rw [hdecomp]
  calc ‖(vmSumChar q χ N - ((if χ = 1 then (N : ℂ) else 0)
          - ∑ z ∈ Efin, (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ)
              * (N : ℂ) ^ z / z))
        - ∑ z ∈ Efin,
            ((analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) - 1) * (N : ℂ) ^ z / z‖
      ≤ ‖vmSumChar q χ N - ((if χ = 1 then (N : ℂ) else 0)
          - ∑ z ∈ Efin, (analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ)
              * (N : ℂ) ^ z / z)‖
        + ‖∑ z ∈ Efin,
            ((analyticOrderNatAt (DirichletCharacter.LFunction χ) z : ℂ) - 1)
              * (N : ℂ) ^ z / z‖ := norm_sub_le _ _
    _ ≤ C * N * Real.exp (-c₁ * x) + 4 * C₂ * (1 + c₂) / κ * N * Real.exp (-(κ / 2) * x) :=
        add_le_add key hcorr
    _ ≤ (C + 4 * C₂ * (1 + c₂) / κ) * N * Real.exp (-min c₁ (κ / 2) * x) := by
        have h1 : Real.exp (-c₁ * x) ≤ Real.exp (-min c₁ (κ / 2) * x) := by
          apply Real.exp_le_exp.mpr
          have := min_le_left c₁ (κ / 2)
          nlinarith
        have h2 : Real.exp (-(κ / 2) * x) ≤ Real.exp (-min c₁ (κ / 2) * x) := by
          apply Real.exp_le_exp.mpr
          have := min_le_right c₁ (κ / 2)
          nlinarith
        have h3 : (0:ℝ) < 4 * C₂ * (1 + c₂) / κ := by positivity
        have e1 : C * (N:ℝ) * Real.exp (-c₁ * x)
            ≤ C * (N:ℝ) * Real.exp (-min c₁ (κ / 2) * x) :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg hC.le hNpos.le)
        have e2 : 4 * C₂ * (1 + c₂) / κ * (N:ℝ) * Real.exp (-(κ / 2) * x)
            ≤ 4 * C₂ * (1 + c₂) / κ * (N:ℝ) * Real.exp (-min c₁ (κ / 2) * x) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg h3.le hNpos.le)
        have e3 : (C + 4 * C₂ * (1 + c₂) / κ) * (N:ℝ) * Real.exp (-min c₁ (κ / 2) * x)
            = C * (N:ℝ) * Real.exp (-min c₁ (κ / 2) * x)
              + 4 * C₂ * (1 + c₂) / κ * (N:ℝ) * Real.exp (-min c₁ (κ / 2) * x) := by ring
        linarith

end SWPort
end

theorem solution : type_of% @SWPort.Davenport.psi_char_of_region_oai := @SWPort.Davenport.psi_char_of_region_oai
