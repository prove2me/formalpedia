-- Prove2me | solution 1 for SWPort.Davenport.zero_free_region
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T20:33:44.175355+00:00
-- url     : https://prove2.me/submissions/9c264678-f339-4c65-a201-62a3caa313c1

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_SWPort_001
import Theorems.Thm_SWPort_Davenport_neg_logDeriv_LFunction_le_sum_zeros
import Theorems.Thm_SWPort_Davenport_neg_logDeriv_trivChar_le_pole
import Theorems.Thm_SWPort_Davenport_zeta_zero_free_region

section
-- module Solutions.Artin.SW.Thm.Davenport_logDeriv_three_four_one
namespace SWPort
/-! Ported from prove2.me: `Davenport.logDeriv_three_four_one` (818312b0-82aa-4b12-91f7-667029fb46de, statement by alya); proof = accepted direct submission f56b6235-b7a1-470a-9dc5-96f5da4f2540 by alya. -/















open Finset DirichletCharacter Vino

/-!
# Davenport §14: the `3-4-1` inequality for logarithmic derivatives

For `σ > 1` and any Dirichlet character `χ` mod `q`,

  `0 ≤ 3 Re(-L'/L(σ, χ₀)) + 4 Re(-L'/L(σ + it, χ)) + Re(-L'/L(σ + 2it, χ²))`.
-/

namespace DavenportLogDeriv341

open Complex ArithmeticFunction
open scoped LSeries.notation

/-- `3 + 4 cos θ + cos 2θ = 2 (1 + cos θ)² ≥ 0`, written for a unit complex number `z`. -/
private lemma three_four_one_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) :
    0 ≤ 3 + 4 * z.re + (z ^ 2).re := by
  have h : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h' : Complex.normSq z = 1 := by
      rw [Complex.normSq_eq_norm_sq, hz]; norm_num
    simpa [Complex.normSq_apply, sq] using h'
  have hz2 : (z ^ 2).re = z.re ^ 2 - z.im ^ 2 := by
    simp [pow_two, Complex.mul_re]
  rw [hz2]
  nlinarith [sq_nonneg (z.re + 1)]

/-- The termwise positivity: for every `n`, the `n`-th terms of the three L-series combine
with weights `3, 4, 1` to something with nonnegative real part. -/
private lemma term_nonneg (q : ℕ) (χ : DirichletCharacter ℂ q) (σ t : ℝ) (n : ℕ) :
    0 ≤ 3 * (LSeries.term (↗(1 : DirichletCharacter ℂ q) * ↗Λ) (σ : ℂ) n).re
      + 4 * (LSeries.term (↗χ * ↗Λ) ((σ : ℂ) + (t : ℂ) * I) n).re
      + (LSeries.term (↗(χ ^ 2) * ↗Λ) ((σ : ℂ) + 2 * (t : ℂ) * I) n).re := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by positivity
  -- the modulus factor `n ^ σ` and the unimodular factor `n ^ (i t)`
  set Np : ℂ := (n : ℂ) ^ (σ : ℂ) with hNp
  set u : ℂ := (n : ℂ) ^ ((t : ℂ) * I) with hu
  have hNpne : Np ≠ 0 := by
    simp only [hNp, ne_eq, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl hn0
  have hune : u ≠ 0 := by
    simp only [hu, ne_eq, Complex.cpow_eq_zero_iff, not_and_or]
    exact Or.inl hn0
  have hsplit1 : (n : ℂ) ^ ((σ : ℂ) + (t : ℂ) * I) = Np * u := Complex.cpow_add _ _ hn0
  have hsplit2 : (n : ℂ) ^ ((σ : ℂ) + 2 * (t : ℂ) * I) = Np * u ^ 2 := by
    rw [show ((σ : ℂ) + 2 * (t : ℂ) * I) = ((σ : ℂ) + (t : ℂ) * I) + (t : ℂ) * I by ring,
      Complex.cpow_add _ _ hn0, hsplit1, hu, sq]
    ring
  -- `Λ n / n ^ σ` is a nonnegative real
  set A : ℝ := (Λ n) / (n : ℝ) ^ σ with hA
  have hA0 : 0 ≤ A := div_nonneg vonMangoldt_nonneg (by positivity)
  have hNpreal : Np = (((n : ℝ) ^ σ : ℝ) : ℂ) := by
    rw [hNp, Complex.ofReal_cpow (le_of_lt hnpos) σ, Complex.ofReal_natCast]
  have hAC : ((A : ℝ) : ℂ) = ((Λ n : ℝ) : ℂ) / Np := by
    rw [hA, hNpreal]
    push_cast
    ring
  -- the unimodular number `z = χ n / n ^ (i t)`
  set z : ℂ := χ n / u with hz
  -- rewrite the three terms
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
  simp only [Pi.mul_apply]
  rw [hsplit1, hsplit2]
  have hchi2 : (χ ^ 2) (n : ZMod q) = (χ (n : ZMod q)) ^ 2 := χ.pow_apply' two_ne_zero _
  rw [hchi2]
  have E1 : χ (n : ZMod q) * ((Λ n : ℝ) : ℂ) / (Np * u) = ((A : ℝ) : ℂ) * z := by
    rw [hAC, hz]; field_simp; try ring
  have E2 : χ (n : ZMod q) ^ 2 * ((Λ n : ℝ) : ℂ) / (Np * u ^ 2) = ((A : ℝ) : ℂ) * z ^ 2 := by
    rw [hAC, hz]; field_simp; try ring
  have E0 : (1 : DirichletCharacter ℂ q) (n : ZMod q) * ((Λ n : ℝ) : ℂ) / Np
      = (1 : DirichletCharacter ℂ q) (n : ZMod q) * ((A : ℝ) : ℂ) := by
    rw [hAC]; ring
  rw [E0, E1, E2]
  by_cases hu' : IsUnit (n : ZMod q)
  · -- `χ₀ n = 1` and `‖z‖ = 1`
    rw [MulChar.one_apply hu', one_mul]
    have hnormu : ‖u‖ = 1 := by
      rw [hu, ← Complex.ofReal_natCast,
        Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
      simp
    have hnormchi : ‖χ (n : ZMod q)‖ = 1 := by
      rw [← hu'.unit_spec, DirichletCharacter.unit_norm_eq_one χ hu'.unit]
    have hnormz : ‖z‖ = 1 := by
      rw [hz, norm_div, hnormu, hnormchi, div_one]
    have key := three_four_one_of_norm_one hnormz
    have h1 : (((A : ℝ) : ℂ)).re = A := Complex.ofReal_re A
    have h2 : (((A : ℝ) : ℂ) * z).re = A * z.re := by
      simp [Complex.mul_re]
    have h3 : (((A : ℝ) : ℂ) * z ^ 2).re = A * (z ^ 2).re := by
      simp [Complex.mul_re]
    rw [h1, h2, h3]
    nlinarith [mul_nonneg hA0 key]
  · -- `χ n = 0 = χ₀ n`
    rw [MulChar.map_nonunit _ hu', MulChar.map_nonunit _ hu'] at *
    simp [hz]

end DavenportLogDeriv341

open DavenportLogDeriv341 in
open scoped LSeries.notation in
theorem _root_.SWPort.Davenport.logDeriv_three_four_one (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ t : ℝ)
    (hσ : 1 < σ) :
    0 ≤ 3 * (-(deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) (σ : ℂ)
              / DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) (σ : ℂ))).re
        + 4 * (-(deriv (DirichletCharacter.LFunction χ) (σ + t * Complex.I)
              / DirichletCharacter.LFunction χ (σ + t * Complex.I))).re
        + (-(deriv (DirichletCharacter.LFunction (χ ^ 2)) (σ + 2 * t * Complex.I)
              / DirichletCharacter.LFunction (χ ^ 2) (σ + 2 * t * Complex.I))).re := by
  have h0 : (1 : ℝ) < ((σ : ℂ)).re := by simpa using hσ
  have h1 : (1 : ℝ) < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by simpa using hσ
  have h2 : (1 : ℝ) < ((σ : ℂ) + 2 * (t : ℂ) * Complex.I).re := by
    simp [Complex.add_re, Complex.mul_re]
    linarith
  have e0 : -(deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) (σ : ℂ)
        / DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) (σ : ℂ))
      = LSeries (↗(1 : DirichletCharacter ℂ q) * ↗ArithmeticFunction.vonMangoldt) (σ : ℂ) := by
    rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq _ h0,
      DirichletCharacter.LFunction_eq_LSeries _ h0,
      DirichletCharacter.deriv_LFunction_eq_deriv_LSeries _ h0, neg_div]
  have e1 : -(deriv (DirichletCharacter.LFunction χ) ((σ : ℂ) + (t : ℂ) * Complex.I)
        / DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * Complex.I))
      = LSeries (↗χ * ↗ArithmeticFunction.vonMangoldt) ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq _ h1,
      DirichletCharacter.LFunction_eq_LSeries _ h1,
      DirichletCharacter.deriv_LFunction_eq_deriv_LSeries _ h1, neg_div]
  have e2 : -(deriv (DirichletCharacter.LFunction (χ ^ 2)) ((σ : ℂ) + 2 * (t : ℂ) * Complex.I)
        / DirichletCharacter.LFunction (χ ^ 2) ((σ : ℂ) + 2 * (t : ℂ) * Complex.I))
      = LSeries (↗(χ ^ 2) * ↗ArithmeticFunction.vonMangoldt)
          ((σ : ℂ) + 2 * (t : ℂ) * Complex.I) := by
    rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq _ h2,
      DirichletCharacter.LFunction_eq_LSeries _ h2,
      DirichletCharacter.deriv_LFunction_eq_deriv_LSeries _ h2, neg_div]
  rw [e0, e1, e2]
  have H0 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt (1 : DirichletCharacter ℂ q) h0
  have H1 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ h1
  have H2 := DirichletCharacter.LSeriesSummable_twist_vonMangoldt (χ ^ 2) h2
  have hs0 := (Complex.hasSum_re H0.hasSum).summable.mul_left 3
  have hs1 := (Complex.hasSum_re H1.hasSum).summable.mul_left 4
  have hs2 := (Complex.hasSum_re H2.hasSum).summable
  rw [LSeries, LSeries, LSeries, Complex.re_tsum H0, Complex.re_tsum H1, Complex.re_tsum H2,
    ← tsum_mul_left, ← tsum_mul_left, ← hs0.tsum_add hs1, ← (hs0.add hs1).tsum_add hs2]
  exact tsum_nonneg fun n => term_nonneg q χ σ t n

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
-- module Solutions.Artin.SW.Thm.Davenport_zero_free_region
namespace SWPort
/-! Ported from prove2.me: `Davenport.zero_free_region` (deb21296-41c0-4d78-90cb-dd1682f5a433, statement by alya); proof = accepted sketch submission 2c2d28d0-8283-4d74-8ae6-8838d91c9fdf by alya. -/
















set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

open Finset DirichletCharacter Vino

namespace Sol

open Complex

/-! ### Conjugation symmetry of Dirichlet L-functions of real characters -/

private lemma LSeries_conj (f : ℕ → ℂ) (s : ℂ) :
    (starRingEnd ℂ) (LSeries f s) = LSeries (fun n => (starRingEnd ℂ) (f n)) ((starRingEnd ℂ) s) := by
  rw [LSeries, LSeries, conj_tsum]
  congr 1
  funext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn, map_div₀]
    congr 1
    have harg : ((n : ℂ)).arg ≠ Real.pi := by
      have : ((n : ℂ)) = ((n : ℝ) : ℂ) := by push_cast; ring
      rw [this, Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
      exact fun h => absurd h.symm (ne_of_gt Real.pi_pos)
    have := Complex.conj_cpow (n : ℂ) ((starRingEnd ℂ) s) harg
    simpa using this.symm

/-- For a real (quadratic) Dirichlet character `χ`, the L-function commutes with complex
conjugation. -/
private lemma LFunction_conj {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (hq : χ.IsQuadratic) (s : ℂ) :
    DirichletCharacter.LFunction χ ((starRingEnd ℂ) s)
      = (starRingEnd ℂ) (DirichletCharacter.LFunction χ s) := by
  set L : ℂ → ℂ := DirichletCharacter.LFunction χ with hL
  have hdiff : Differentiable ℂ L := DirichletCharacter.differentiable_LFunction hχ
  set F : ℂ → ℂ := fun z => (starRingEnd ℂ) (L ((starRingEnd ℂ) z)) with hF
  have hFdiff : Differentiable ℂ F := by
    intro z
    have := (hdiff ((starRingEnd ℂ) z)).conj_conj
    simpa [hF, Function.comp_def] using this
  -- the two entire functions agree near `2`
  have hagree : F =ᶠ[nhds (2 : ℂ)] L := by
    have hopen : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
    have hmem : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by norm_num
    filter_upwards [hopen.mem_nhds hmem] with z hz
    have hz' : 1 < ((starRingEnd ℂ) z).re := by simpa using hz
    have h1 : L z = LSeries (fun n : ℕ => χ n) z :=
      DirichletCharacter.LFunction_eq_LSeries χ hz
    have h2 : L ((starRingEnd ℂ) z) = LSeries (fun n : ℕ => χ n) ((starRingEnd ℂ) z) :=
      DirichletCharacter.LFunction_eq_LSeries χ hz'
    have hreal : (fun n : ℕ => (starRingEnd ℂ) (χ n)) = (fun n : ℕ => χ n) := by
      funext n
      rcases hq (n : ZMod q) with h | h | h <;> simp [h]
    have := LSeries_conj (fun n : ℕ => χ n) ((starRingEnd ℂ) z)
    rw [hreal] at this
    simp only [hF, h2, this, Complex.conj_conj, h1]
  have hEq : Set.EqOn F L Set.univ := by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (fun x _ => hFdiff.analyticAt x) (fun x _ => hdiff.analyticAt x)
      isPreconnected_univ (Set.mem_univ (2 : ℂ)) hagree
  have h := hEq (Set.mem_univ ((starRingEnd ℂ) s))
  simp only [hF, Complex.conj_conj] at h
  exact h.symm

/-! ### The real-arithmetic contradictions -/

/-- Case of a complex character (`χ² ≠ 1`). -/
private lemma arith1_p0 (δ ℓ u c K : ℝ) (hδ : 0 < δ) (hℓ : 0 < ℓ) (hu : 0 < u)
    (hK : 0 ≤ K) (hKδ : K * δ ≤ 1 / 2) (hc0 : 0 < c) (hc : c ≤ δ / 8)
    (h1 : 4 * (1 / u) ≤ 3 * (ℓ / δ) + K * ℓ) (h2 : u * ℓ ≤ δ + c) : False := by
  have hul : 0 < u * ℓ := mul_pos hu hℓ
  have h4 : (4 : ℝ) / u ≤ 3 * (ℓ / δ) + K * ℓ := by
    rw [div_eq_mul_inv, ← one_div]; linarith
  rw [div_le_iff₀ hu] at h4
  have hkey : 4 * δ ≤ (u * ℓ) * (3 + K * δ) := by
    have h5 := mul_le_mul_of_nonneg_right h4 hδ.le
    have h6 : (3 * (ℓ / δ) + K * ℓ) * u * δ = (u * ℓ) * (3 + K * δ) := by
      field_simp
    linarith [h5, h6.le, h6.ge]
  nlinarith [hkey, h2, hKδ, hc, hδ, hul, hc0]

/-- Case of a real character with a complex zero of height `|γ| ≥ δ / ℓ`. -/
private lemma arith2a (δ ℓ u c K : ℝ) (hδ : 0 < δ) (hℓ : 0 < ℓ) (hu : 0 < u)
    (hK : 0 ≤ K) (hKδ : K * δ ≤ 1 / 8) (hc0 : 0 < c) (hc : c ≤ δ / 8)
    (h1 : 4 * (1 / u) ≤ (13 / 4) * (ℓ / δ) + K * ℓ) (h2 : u * ℓ ≤ δ + c) : False := by
  have hul : 0 < u * ℓ := mul_pos hu hℓ
  have h4 : (4 : ℝ) / u ≤ (13 / 4) * (ℓ / δ) + K * ℓ := by
    rw [div_eq_mul_inv, ← one_div]; linarith
  rw [div_le_iff₀ hu] at h4
  have hkey : 4 * δ ≤ (u * ℓ) * (13 / 4 + K * δ) := by
    have h5 := mul_le_mul_of_nonneg_right h4 hδ.le
    have h6 : ((13 / 4) * (ℓ / δ) + K * ℓ) * u * δ = (u * ℓ) * (13 / 4 + K * δ) := by
      field_simp
    linarith [h5, h6.le, h6.ge]
  nlinarith [hkey, h2, hKδ, hc, hδ, hul, hc0]

/-- Case of a real character with a zero very close to the real axis: `S` is the sum of the
`Re (1/(σ - ρ))` over the (one or two) zeros used. -/
private lemma arith2bc (δ ℓ c K S : ℝ) (hδ : 0 < δ) (hℓ : 0 < ℓ)
    (hK : 0 ≤ K) (hKδ : K * δ ≤ 1 / 20) (hc0 : 0 < c) (hc : c ≤ δ / 8)
    (hS1 : (8 / 5) * ℓ / (2 * δ + c) ≤ S) (hS2 : S ≤ (1 / 2) * (ℓ / δ) + K * ℓ) : False := by
  have hd : 0 < 2 * δ + c := by linarith
  have h1 : (8 / 5) * ℓ / (2 * δ + c) ≤ (1 / 2) * (ℓ / δ) + K * ℓ := le_trans hS1 hS2
  rw [div_le_iff₀ hd] at h1
  -- h1 : (8/5) * ℓ ≤ ((1/2) * ℓ / δ + K * ℓ) * (2 * δ + c)
  have h2 := mul_le_mul_of_nonneg_right h1 hδ.le
  have h3 : ((1 / 2) * (ℓ / δ) + K * ℓ) * (2 * δ + c) * δ
      = ℓ * ((2 * δ + c) * (1 / 2 + K * δ)) := by field_simp
  rw [h3] at h2
  -- h2 : (8/5) * ℓ * δ ≤ ℓ * ((2δ + c) * (1/2 + Kδ))
  have h4 : (8 / 5) * δ ≤ (2 * δ + c) * (1 / 2 + K * δ) := by
    refine le_of_mul_le_mul_left ?_ hℓ
    linarith
  nlinarith [h4, hKδ, hc, hδ, hc0]

/-! ### Elementary facts about the region -/

private lemma log_two_le_p1 (q : ℕ) [NeZero q] (t : ℝ) :
    Real.log 2 ≤ Real.log ((q : ℝ) * (|t| + 2)) := by
  have hq : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have : (2 : ℝ) ≤ (q : ℝ) * (|t| + 2) := by nlinarith [abs_nonneg t]
  exact Real.log_le_log (by norm_num) this

private lemma log_two_pos' : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)

private lemma log_double_le (q : ℕ) [NeZero q] (t : ℝ) :
    Real.log ((q : ℝ) * (|2 * t| + 2)) ≤ 2 * Real.log ((q : ℝ) * (|t| + 2)) := by
  have hq : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hbase : (0 : ℝ) < (q : ℝ) * (|t| + 2) := by nlinarith [abs_nonneg t]
  have h1 : ((q : ℝ) * (|2 * t| + 2)) ≤ 2 * ((q : ℝ) * (|t| + 2)) := by
    rw [abs_mul]
    have : |(2 : ℝ)| = 2 := by norm_num
    rw [this]
    nlinarith [abs_nonneg t]
  have h2 : Real.log ((q : ℝ) * (|2 * t| + 2)) ≤ Real.log (2 * ((q : ℝ) * (|t| + 2))) :=
    Real.log_le_log (by nlinarith [abs_nonneg (2 * t)]) h1
  rw [Real.log_mul (by norm_num) (ne_of_gt hbase)] at h2
  have h3 := log_two_le_p1 q t
  linarith

/-- At a zero of an entire `L`-function the analytic order is at least one. -/
private lemma one_le_order_p0 {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {ρ : ℂ} (h : DirichletCharacter.LFunction χ ρ = 0) :
    (1 : ℕ∞) ≤ analyticOrderAt (DirichletCharacter.LFunction χ) ρ := by
  have ha : AnalyticAt ℂ (DirichletCharacter.LFunction χ) ρ :=
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt ρ
  have : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨ha, h⟩
  exact ENat.one_le_iff_ne_zero.mpr this

/-- At a zero where the derivative also vanishes, the analytic order is at least two. -/
private lemma two_le_order {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {ρ : ℂ} (h : DirichletCharacter.LFunction χ ρ = 0)
    (h' : deriv (DirichletCharacter.LFunction χ) ρ = 0) :
    (2 : ℕ∞) ≤ analyticOrderAt (DirichletCharacter.LFunction χ) ρ := by
  have ha : AnalyticAt ℂ (DirichletCharacter.LFunction χ) ρ :=
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt ρ
  have key := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := 2) ha).mpr ?_
  · exact_mod_cast key
  · intro i hi
    interval_cases i
    · simpa using h
    · simpa [iteratedDeriv_one] using h'

/-! ### Abbreviations for the hypotheses coming from the child theorems -/

/-! ### The three zero-free arguments -/


/-- A non-principal character with `χ² ≠ 1` has no zero in the region. -/
private lemma case_complex
    (c₀ cZ δ c K : ℝ)
    (hc₀ : 0 ≤ c₀) (hcZ : 0 < cZ)
    (hδ : 0 < δ) (hδ8 : δ ≤ Real.log 2 / 8) (hc0 : 0 < c) (hc : c ≤ δ / 8)
    (hK : 0 ≤ K) (hKδ : K * δ ≤ 1 / 20)
    (hKbig : 3 * c₀ / Real.log 2 + 6 * cZ ≤ K)
    (Htriv : TrivBound c₀) (Hzeros : ZerosBound cZ)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hχ2 : χ ^ 2 ≠ 1)
    (ρ : ℂ) (hreg : Davenport.InRegion c q ρ)
    (hzero : DirichletCharacter.LFunction χ ρ = 0) : False := by
  have hl2pos : (0 : ℝ) < Real.log 2 := log_two_pos'
  obtain ⟨β, hβ⟩ : ∃ x : ℝ, ρ.re = x := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ x : ℝ, ρ.im = x := ⟨_, rfl⟩
  obtain ⟨ℓ, hℓ⟩ : ∃ x : ℝ, Real.log ((q : ℝ) * (|γ| + 2)) = x := ⟨_, rfl⟩
  have hℓ2 : Real.log 2 ≤ ℓ := hℓ ▸ log_two_le_p1 q γ
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le hl2pos hℓ2
  have hβ1 : β < 1 := by
    by_contra h
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
      (by rw [hβ]; exact not_lt.mp h)) hzero
  have hreg' : 1 - c / ℓ ≤ β := by
    have h := hreg
    simp only [Davenport.InRegion, Davenport.regionBoundary] at h
    rw [hγ, hℓ, hβ] at h
    exact h
  obtain ⟨σ, hσ⟩ : ∃ x : ℝ, x = 1 + δ / ℓ := ⟨_, rfl⟩
  have hdl0 : 0 < δ / ℓ := div_pos hδ hℓ0
  have hdl : δ / ℓ ≤ 1 / 8 := by
    rw [div_le_div_iff₀ hℓ0 (by norm_num)]; nlinarith
  have hσ1 : 1 < σ := by rw [hσ]; linarith
  have hσ2 : σ ≤ 2 := by rw [hσ]; linarith
  obtain ⟨u, hu⟩ : ∃ x : ℝ, x = σ - β := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; linarith
  have hbc : (1 - β) * ℓ ≤ c := by
    have h1 : 1 - β ≤ c / ℓ := by linarith
    have h2 := mul_le_mul_of_nonneg_right h1 hℓ0.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hℓ0)] at h2
  have hul : u * ℓ = δ + (1 - β) * ℓ := by
    rw [hu, hσ]; field_simp; ring
  have hu2 : u * ℓ ≤ δ + c := by rw [hul]; linarith
  have husmall : u ≤ 1 / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hℓ2 hu0.le, hl2pos, hu2, hδ8, hc, hδ]
  obtain ⟨s, hs⟩ : ∃ z : ℂ, z = (σ : ℂ) + (γ : ℂ) * Complex.I := ⟨_, rfl⟩
  have hsre : s.re = σ := by rw [hs]; simp
  have hsim : s.im = γ := by rw [hs]; simp
  have hsρ : s - ρ = ((u : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.sub_re, hsre, hβ, hu, Complex.ofReal_re]
    · rw [Complex.sub_im, hsim, hγ, Complex.ofReal_im]; ring
  have hρs : ρ - s = ((-u : ℝ) : ℂ) := by
    have h : ρ - s = -(s - ρ) := by ring
    rw [h, hsρ]; push_cast; ring
  have hB := Hzeros q χ hχ s (by rw [hsre]; exact hσ1) (by rw [hsre]; exact hσ2)
    ({ρ} : Multiset ℂ) (by
      intro x hx
      rw [Multiset.mem_singleton] at hx
      rw [hx, hρs, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg hu0.le]
      linarith)
    (by
      intro x
      by_cases hx : x = ρ
      · rw [hx, Multiset.count_singleton_self]
        exact_mod_cast one_le_order_p0 hχ hzero
      · rw [Multiset.count_singleton, if_neg hx]
        simp)
  rw [hsim, hℓ, Multiset.map_singleton, Multiset.sum_singleton, hsρ] at hB
  have hinv : ((1 : ℂ) / ((u : ℝ) : ℂ)).re = 1 / u := by
    rw [show (1 : ℂ) / ((u : ℝ) : ℂ) = (((1 / u : ℝ)) : ℂ) by push_cast; ring]
    exact Complex.ofReal_re _
  rw [hinv] at hB
  obtain ⟨s₂, hs₂⟩ : ∃ z : ℂ, z = (σ : ℂ) + 2 * (γ : ℂ) * Complex.I := ⟨_, rfl⟩
  have hs₂re : s₂.re = σ := by rw [hs₂]; simp
  have hs₂im : s₂.im = 2 * γ := by rw [hs₂]; simp
  have hC := Hzeros q (χ ^ 2) hχ2 s₂ (by rw [hs₂re]; exact hσ1) (by rw [hs₂re]; exact hσ2)
    (0 : Multiset ℂ) (by simp) (by simp)
  rw [hs₂im] at hC
  simp only [Multiset.map_zero, Multiset.sum_zero, sub_zero] at hC
  have hClog := log_double_le q γ
  rw [hℓ] at hClog
  have hC' : (-(deriv (DirichletCharacter.LFunction (χ ^ 2)) s₂
      / DirichletCharacter.LFunction (χ ^ 2) s₂)).re ≤ 2 * (cZ * ℓ) := by
    refine hC.trans ?_
    nlinarith [hClog, hcZ]
  have hA := Htriv q σ hσ1 hσ2
  have hσm1 : σ - 1 = δ / ℓ := by rw [hσ]; ring
  rw [hσm1, one_div_div] at hA
  have h341 := Davenport.logDeriv_three_four_one q χ σ γ hσ1
  rw [← hs, ← hs₂] at h341
  have hfin : 3 * c₀ + 6 * (cZ * ℓ) ≤ K * ℓ := by
    have h1 : 3 * c₀ ≤ (3 * c₀ / Real.log 2) * ℓ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2pos]; nlinarith
    have h2 : (3 * c₀ / Real.log 2 + 6 * cZ) * ℓ ≤ K * ℓ :=
      mul_le_mul_of_nonneg_right hKbig hℓ0.le
    nlinarith [h1, h2]
  have hmain : 4 * (1 / u) ≤ 3 * (ℓ / δ) + K * ℓ := by linarith [h341, hA, hB, hC', hfin]
  exact arith1_p0 δ ℓ u c K hδ hℓ0 hu0 hK (by linarith) hc0 hc hmain hu2


/-- A real non-principal character has no zero in the region at height `|γ| ≥ δ / ℓ`. -/
private lemma case_real_high
    (c₀ cZ cP δ c K : ℝ)
    (hc₀ : 0 ≤ c₀) (hcZ : 0 < cZ) (hcP : 0 < cP)
    (hδ : 0 < δ) (hδ8 : δ ≤ Real.log 2 / 8) (hc0 : 0 < c) (hc : c ≤ δ / 8)
    (hK : 0 ≤ K) (hKδ : K * δ ≤ 1 / 20)
    (hKbig : 3 * c₀ / Real.log 2 + 4 * cZ + 2 * cP ≤ K)
    (Htriv : TrivBound c₀) (Hpole : PoleBound cP) (Hzeros : ZerosBound cZ)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hsq : χ ^ 2 = 1)
    (ρ : ℂ) (hreg : Davenport.InRegion c q ρ)
    (hzero : DirichletCharacter.LFunction χ ρ = 0)
    (hhigh : δ / Real.log ((q : ℝ) * (|ρ.im| + 2)) ≤ |ρ.im|) : False := by
  have hl2pos : (0 : ℝ) < Real.log 2 := log_two_pos'
  obtain ⟨β, hβ⟩ : ∃ x : ℝ, ρ.re = x := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ x : ℝ, ρ.im = x := ⟨_, rfl⟩
  rw [hγ] at hhigh
  obtain ⟨ℓ, hℓ⟩ : ∃ x : ℝ, Real.log ((q : ℝ) * (|γ| + 2)) = x := ⟨_, rfl⟩
  rw [hℓ] at hhigh
  have hℓ2 : Real.log 2 ≤ ℓ := hℓ ▸ log_two_le_p1 q γ
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le hl2pos hℓ2
  have hβ1 : β < 1 := by
    by_contra h
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
      (by rw [hβ]; exact not_lt.mp h)) hzero
  have hreg' : 1 - c / ℓ ≤ β := by
    have h := hreg
    simp only [Davenport.InRegion, Davenport.regionBoundary] at h
    rw [hγ, hℓ, hβ] at h
    exact h
  obtain ⟨p, hp⟩ : ∃ x : ℝ, δ / ℓ = x := ⟨_, rfl⟩
  have hp0 : 0 < p := hp ▸ div_pos hδ hℓ0
  have hp8 : p ≤ 1 / 8 := by
    rw [← hp, div_le_div_iff₀ hℓ0 (by norm_num)]; nlinarith
  have hpℓ : p * ℓ = δ := by rw [← hp]; field_simp
  have hinvp : 1 / p = ℓ / δ := by rw [← hp, one_div_div]
  rw [hp] at hhigh
  obtain ⟨σ, hσ⟩ : ∃ x : ℝ, x = 1 + p := ⟨_, rfl⟩
  have hσ1 : 1 < σ := by rw [hσ]; linarith
  have hσ2 : σ ≤ 2 := by rw [hσ]; linarith
  have hσm1 : σ - 1 = p := by rw [hσ]; ring
  obtain ⟨u, hu⟩ : ∃ x : ℝ, x = σ - β := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; linarith
  have hbc : (1 - β) * ℓ ≤ c := by
    have h1 : 1 - β ≤ c / ℓ := by linarith
    have h2 := mul_le_mul_of_nonneg_right h1 hℓ0.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hℓ0)] at h2
  have hul : u * ℓ = δ + (1 - β) * ℓ := by rw [hu, hσ, ← hpℓ]; ring
  have hu2 : u * ℓ ≤ δ + c := by rw [hul]; linarith
  have husmall : u ≤ 1 / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hℓ2 hu0.le, hl2pos, hu2, hδ8, hc, hδ]
  obtain ⟨s, hs⟩ : ∃ z : ℂ, z = (σ : ℂ) + (γ : ℂ) * Complex.I := ⟨_, rfl⟩
  have hsre : s.re = σ := by rw [hs]; simp
  have hsim : s.im = γ := by rw [hs]; simp
  have hsρ : s - ρ = ((u : ℝ) : ℂ) := by
    apply Complex.ext
    · rw [Complex.sub_re, hsre, hβ, hu, Complex.ofReal_re]
    · rw [Complex.sub_im, hsim, hγ, Complex.ofReal_im]; ring
  have hρs : ρ - s = ((-u : ℝ) : ℂ) := by
    have h : ρ - s = -(s - ρ) := by ring
    rw [h, hsρ]; push_cast; ring
  have hB := Hzeros q χ hχ s (by rw [hsre]; exact hσ1) (by rw [hsre]; exact hσ2)
    ({ρ} : Multiset ℂ) (by
      intro x hx
      rw [Multiset.mem_singleton] at hx
      rw [hx, hρs, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg hu0.le]
      linarith)
    (by
      intro x
      by_cases hx : x = ρ
      · rw [hx, Multiset.count_singleton_self]
        exact_mod_cast one_le_order_p0 hχ hzero
      · rw [Multiset.count_singleton, if_neg hx]
        simp)
  rw [hsim, hℓ, Multiset.map_singleton, Multiset.sum_singleton, hsρ] at hB
  have hinv : ((1 : ℂ) / ((u : ℝ) : ℂ)).re = 1 / u := by
    rw [show (1 : ℂ) / ((u : ℝ) : ℂ) = (((1 / u : ℝ)) : ℂ) by push_cast; ring]
    exact Complex.ofReal_re _
  rw [hinv] at hB
  obtain ⟨s₂, hs₂⟩ : ∃ z : ℂ, z = (σ : ℂ) + 2 * (γ : ℂ) * Complex.I := ⟨_, rfl⟩
  have hs₂re : s₂.re = σ := by rw [hs₂]; simp
  have hs₂im : s₂.im = 2 * γ := by rw [hs₂]; simp
  have hz1 : (s₂ - 1).re = p := by
    rw [Complex.sub_re, hs₂re, Complex.one_re, hσ]; ring
  have hz2 : (s₂ - 1).im = 2 * γ := by rw [Complex.sub_im, hs₂im, Complex.one_im]; ring
  have hzre : ((1 : ℂ) / (s₂ - 1)).re = p / (p * p + (2 * γ) * (2 * γ)) := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply, hz1, hz2]
  have hsq' : p * p ≤ γ * γ := by
    have h := mul_self_le_mul_self hp0.le hhigh
    rwa [abs_mul_abs_self] at h
  have hden : 0 < p * p + (2 * γ) * (2 * γ) := by
    have h1 := mul_pos hp0 hp0
    have h2 := mul_self_nonneg (2 * γ)
    linarith only [h1, h2]
  have hpb : ((1 : ℂ) / (s₂ - 1)).re ≤ (1 / 4) * (ℓ / δ) := by
    rw [hzre, ← hinvp, show (1 : ℝ) / 4 * (1 / p) = 1 / (4 * p) by ring,
      div_le_div_iff₀ hden (by positivity)]
    linarith only [hsq', mul_self_nonneg p]
  have hCp := Hpole q s₂ (by rw [hs₂re]; exact hσ1) (by rw [hs₂re]; exact hσ2)
  rw [hs₂im] at hCp
  have hClog := log_double_le q γ
  rw [hℓ] at hClog
  have hC' : (-(deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) s₂
      / DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s₂)).re
      ≤ (1 / 4) * (ℓ / δ) + 2 * (cP * ℓ) := by
    refine hCp.trans ?_
    nlinarith [hpb, hClog, hcP]
  have hA := Htriv q σ hσ1 hσ2
  rw [hσm1, hinvp] at hA
  have h341 := Davenport.logDeriv_three_four_one q χ σ γ hσ1
  rw [← hs, ← hs₂, hsq] at h341
  have hfin : 3 * c₀ + 4 * (cZ * ℓ) + 2 * (cP * ℓ) ≤ K * ℓ := by
    have h0 : 3 * c₀ * Real.log 2 ≤ 3 * c₀ * ℓ :=
      mul_le_mul_of_nonneg_left hℓ2 (by linarith only [hc₀])
    have h1 : 3 * c₀ ≤ (3 * c₀ / Real.log 2) * ℓ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2pos]
      linarith only [h0]
    have h2 : (3 * c₀ / Real.log 2 + 4 * cZ + 2 * cP) * ℓ ≤ K * ℓ :=
      mul_le_mul_of_nonneg_right hKbig hℓ0.le
    linarith only [h1, h2]
  have hmain : 4 * (1 / u) ≤ (13 / 4) * (ℓ / δ) + K * ℓ := by
    linarith only [h341, hA, hB, hC', hfin]
  exact arith2a δ ℓ u c K hδ hℓ0 hu0 hK (by linarith) hc0 hc hmain hu2

/-- The basic upper bound for the sum `∑ Re (1/(σ - ρ))` over zeros, at a real abscissa
`σ = 1 + 2δ/ℓ`, for a real non-principal character. -/
private lemma real_axis_bound
    (c₀ cZ δ c K : ℝ) (hc₀ : 0 ≤ c₀) (hcZ : 0 < cZ)
    (hδ : 0 < δ) (hK : 0 ≤ K) (hKbig : c₀ / Real.log 2 + cZ ≤ K)
    (Htriv : TrivBound c₀) (Hzeros : ZerosBound cZ)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hsq : χ ^ 2 = 1)
    (ℓ σ : ℝ) (hℓ2 : Real.log 2 ≤ ℓ) (hℓ0 : 0 < ℓ)
    (hℓq : Real.log ((q : ℝ) * (0 + 2)) ≤ ℓ)
    (hσm1 : σ - 1 = 2 * δ / ℓ) (hσ1 : 1 < σ) (hσ2 : σ ≤ 2)
    (Z : Multiset ℂ) (hZ : ∀ ρ ∈ Z, ‖ρ - (σ : ℂ)‖ ≤ 1 / 2)
    (hcount : ∀ ρ : ℂ, (Z.count ρ : ℕ∞) ≤ analyticOrderAt (DirichletCharacter.LFunction χ) ρ) :
    (Z.map fun ρ => (1 / ((σ : ℂ) - ρ)).re).sum ≤ (1 / 2) * (ℓ / δ) + K * ℓ := by
  have hl2pos : (0 : ℝ) < Real.log 2 := log_two_pos'
  have hB := Hzeros q χ hχ ((σ : ℝ) : ℂ)
    (by rw [Complex.ofReal_re]; exact hσ1) (by rw [Complex.ofReal_re]; exact hσ2) Z hZ hcount
  rw [Complex.ofReal_im, abs_zero] at hB
  have hA := Htriv q σ hσ1 hσ2
  rw [hσm1, one_div_div] at hA
  have h341 := Davenport.logDeriv_three_four_one q χ σ 0 hσ1
  have e1 : ((σ : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I = ((σ : ℝ) : ℂ) := by simp
  have e2 : ((σ : ℝ) : ℂ) + 2 * ((0 : ℝ) : ℂ) * Complex.I = ((σ : ℝ) : ℂ) := by simp
  rw [e1, e2, hsq] at h341
  have hfin : c₀ + cZ * ℓ ≤ K * ℓ := by
    have h0 : c₀ * Real.log 2 ≤ c₀ * ℓ := mul_le_mul_of_nonneg_left hℓ2 hc₀
    have h1 : c₀ ≤ (c₀ / Real.log 2) * ℓ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hl2pos]
      linarith only [h0]
    have h2 : (c₀ / Real.log 2 + cZ) * ℓ ≤ K * ℓ := mul_le_mul_of_nonneg_right hKbig hℓ0.le
    linarith only [h1, h2]
  have hcZℓ : cZ * Real.log ((q : ℝ) * (0 + 2)) ≤ cZ * ℓ :=
    mul_le_mul_of_nonneg_left hℓq hcZ.le
  have hhalf : ℓ / (2 * δ) = (1 / 2) * (ℓ / δ) := by ring
  rw [hhalf] at hA
  have key : (Multiset.map (fun ρ => (1 / (((σ : ℝ) : ℂ) - ρ)).re) Z).sum
      ≤ cZ * Real.log ((q : ℝ) * (0 + 2))
        + (-(deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) ((σ : ℝ) : ℂ)
            / DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) ((σ : ℝ) : ℂ))).re := by
    linarith only [h341, hB]
  have step1 := key.trans (add_le_add hcZℓ (le_refl _))
  have step2 : cZ * ℓ
      + (-(deriv (DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q)) ((σ : ℝ) : ℂ)
          / DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) ((σ : ℝ) : ℂ))).re
      ≤ (1 / 2) * (ℓ / δ) + K * ℓ := by
    linarith only [hA, hfin]
  exact step1.trans step2


/-- A real non-principal character has no zero in the region at height `0 < |γ| ≤ δ / ℓ`. -/
private lemma case_real_low
    (c₀ cZ δ c K : ℝ) (hc₀ : 0 ≤ c₀) (hcZ : 0 < cZ)
    (hδ : 0 < δ) (hδ8 : δ ≤ Real.log 2 / 8) (hc0 : 0 < c) (hc : c ≤ δ / 8)
    (hK : 0 ≤ K) (hKδ : K * δ ≤ 1 / 20) (hKbig : c₀ / Real.log 2 + cZ ≤ K)
    (Htriv : TrivBound c₀) (Hzeros : ZerosBound cZ)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hquad : χ.IsQuadratic)
    (ρ : ℂ) (hreg : Davenport.InRegion c q ρ)
    (hzero : DirichletCharacter.LFunction χ ρ = 0) (hγ0 : ρ.im ≠ 0)
    (hlow : |ρ.im| ≤ δ / Real.log ((q : ℝ) * (|ρ.im| + 2))) : False := by
  have hl2pos : (0 : ℝ) < Real.log 2 := log_two_pos'
  have hsq : χ ^ 2 = 1 := hquad.sq_eq_one
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  obtain ⟨β, hβ⟩ : ∃ x : ℝ, ρ.re = x := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ x : ℝ, ρ.im = x := ⟨_, rfl⟩
  rw [hγ] at hlow hγ0
  obtain ⟨ℓ, hℓ⟩ : ∃ x : ℝ, Real.log ((q : ℝ) * (|γ| + 2)) = x := ⟨_, rfl⟩
  rw [hℓ] at hlow
  have hℓ2 : Real.log 2 ≤ ℓ := hℓ ▸ log_two_le_p1 q γ
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le hl2pos hℓ2
  have hℓq : Real.log ((q : ℝ) * (0 + 2)) ≤ ℓ := by
    rw [← hℓ]
    exact Real.log_le_log (by nlinarith [hq1]) (by nlinarith [hq1, abs_nonneg γ])
  have hβ1 : β < 1 := by
    by_contra h
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
      (by rw [hβ]; exact not_lt.mp h)) hzero
  have hreg' : 1 - c / ℓ ≤ β := by
    have h := hreg
    simp only [Davenport.InRegion, Davenport.regionBoundary] at h
    rw [hγ, hℓ, hβ] at h
    exact h
  -- the abscissa `σ = 1 + 2δ/ℓ`
  obtain ⟨p, hp⟩ : ∃ x : ℝ, 2 * δ / ℓ = x := ⟨_, rfl⟩
  have hp0 : 0 < p := hp ▸ div_pos (by linarith only [hδ]) hℓ0
  have hp4 : p ≤ 1 / 4 := by
    rw [← hp, div_le_div_iff₀ hℓ0 (by norm_num)]; linarith only [hδ8, hℓ2]
  have hpℓ : p * ℓ = 2 * δ := by rw [← hp]; field_simp
  obtain ⟨σ, hσ⟩ : ∃ x : ℝ, x = 1 + p := ⟨_, rfl⟩
  have hσ1 : 1 < σ := by rw [hσ]; linarith only [hp0]
  have hσ2 : σ ≤ 2 := by rw [hσ]; linarith only [hp4]
  have hσm1 : σ - 1 = 2 * δ / ℓ := by rw [hσ, hp]; ring
  obtain ⟨u, hu⟩ : ∃ x : ℝ, x = σ - β := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; linarith only [hσ1, hβ1]
  have hbc : (1 - β) * ℓ ≤ c := by
    have h1 : 1 - β ≤ c / ℓ := by linarith only [hreg']
    have h2 := mul_le_mul_of_nonneg_right h1 hℓ0.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hℓ0)] at h2
  have hul : u * ℓ = 2 * δ + (1 - β) * ℓ := by rw [hu, hσ, ← hpℓ]; ring
  have hu2 : u * ℓ ≤ 2 * δ + c := by rw [hul]; linarith only [hbc]
  have hup : p ≤ u := by rw [hu, hσ]; linarith only [hβ1]
  -- the zero is close to the real axis
  have hγℓ : |γ| * ℓ ≤ δ := by
    have h := mul_le_mul_of_nonneg_right hlow hℓ0.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hℓ0)] at h
  have hγu : 2 * |γ| ≤ u := by
    have h1 : (2 * |γ|) * ℓ ≤ 2 * δ := by linarith only [hγℓ]
    have h2 : p * ℓ ≤ u * ℓ := mul_le_mul_of_nonneg_right hup hℓ0.le
    rw [hpℓ] at h2
    exact le_of_mul_le_mul_right (by linarith only [h1, h2]) hℓ0
  have husmall : u ≤ 17 / 64 := by
    have h2 : u * Real.log 2 ≤ u * ℓ := mul_le_mul_of_nonneg_left hℓ2 hu0.le
    have h3 : u * Real.log 2 ≤ (17 / 64) * Real.log 2 := by
      linarith only [h2, hu2, hδ8, hc]
    exact le_of_mul_le_mul_right h3 hl2pos
  -- the conjugate zero
  obtain ⟨ρ', hρ'⟩ : ∃ z : ℂ, z = (starRingEnd ℂ) ρ := ⟨_, rfl⟩
  have hzero' : DirichletCharacter.LFunction χ ρ' = 0 := by
    rw [hρ', LFunction_conj χ hχ hquad ρ, hzero, map_zero]
  have hne : ρ ≠ ρ' := by
    rw [hρ']
    intro h
    apply hγ0
    have h2 := congrArg Complex.im h
    rw [Complex.conj_im, hγ] at h2
    linarith only [h2]
  have hρ're : ρ'.re = β := by rw [hρ', Complex.conj_re, hβ]
  have hρ'im : ρ'.im = -γ := by rw [hρ', Complex.conj_im, hγ]
  -- the two points are within distance 1/2 of σ
  have hdist : ∀ x : ℂ, x.re = β → |x.im| = |γ| → ‖x - (σ : ℂ)‖ ≤ 1 / 2 := by
    intro x hxre hxim
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, hxre, sub_zero,
      hxim, abs_of_nonpos (by linarith only [hu, hu0] : β - σ ≤ 0)]
    linarith only [hu, hγu, husmall]
  -- the real parts of `1/(σ - ρ)` and `1/(σ - ρ')`
  have hre1 : ((1 : ℂ) / ((σ : ℂ) - ρ)).re = u / (u * u + γ * γ) := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, hβ, hγ, ← hu]
    ring_nf
  have hre2 : ((1 : ℂ) / ((σ : ℂ) - ρ')).re = u / (u * u + γ * γ) := by
    rw [one_div, Complex.inv_re, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, hρ're, hρ'im, ← hu]
    ring_nf
  -- apply the real-axis bound with `Z = {ρ, conj ρ}`
  have hbound := real_axis_bound c₀ cZ δ c K hc₀ hcZ hδ hK hKbig Htriv Hzeros q χ hχ hsq ℓ σ
    hℓ2 hℓ0 hℓq hσm1 hσ1 hσ2 ({ρ, ρ'} : Multiset ℂ)
    (by
      intro x hx
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hdist x hβ (by rw [hγ])
      · exact hdist x hρ're (by rw [hρ'im, abs_neg]))
    (by
      intro x
      by_cases h1 : x = ρ
      · rw [h1]
        have hcnt : ({ρ, ρ'} : Multiset ℂ).count ρ = 1 := by
          simp [Multiset.insert_eq_cons, Multiset.count_singleton, hne, Ne.symm hne, eq_comm]
        rw [hcnt]
        exact_mod_cast one_le_order_p0 hχ hzero
      · by_cases h2 : x = ρ'
        · rw [h2]
          have hcnt : ({ρ, ρ'} : Multiset ℂ).count ρ' = 1 := by
            simp [Multiset.insert_eq_cons, Multiset.count_singleton, hne, Ne.symm hne, eq_comm]
          rw [hcnt]
          exact_mod_cast one_le_order_p0 hχ hzero'
        · have hcnt : ({ρ, ρ'} : Multiset ℂ).count x = 0 := by
            simp [Multiset.insert_eq_cons, Multiset.count_singleton, h1, h2, eq_comm]
          rw [hcnt]; simp)
  have hsum : (({ρ, ρ'} : Multiset ℂ).map fun r => ((1 : ℂ) / ((σ : ℂ) - r)).re).sum
      = u / (u * u + γ * γ) + u / (u * u + γ * γ) := by
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
      Multiset.map_singleton, Multiset.sum_singleton, hre1, hre2]
  rw [hsum] at hbound
  -- lower bound for the sum
  have huu : 0 < u * u := mul_pos hu0 hu0
  have hden : 0 < u * u + γ * γ := by
    have := mul_self_nonneg γ
    linarith only [huu, this]
  have hγsq : 4 * (γ * γ) ≤ u * u := by
    have h : (2 * |γ|) * (2 * |γ|) ≤ u * u := mul_self_le_mul_self (by positivity) hγu
    have h2 : |γ| * |γ| = γ * γ := abs_mul_abs_self γ
    linarith only [h, h2]
  have hlow2 : (8 / 5) * ℓ / (2 * δ + c) ≤ u / (u * u + γ * γ) + u / (u * u + γ * γ) := by
    have hd : (0 : ℝ) < 2 * δ + c := by linarith only [hδ, hc0]
    have hstep : (8 / 5) / u ≤ u / (u * u + γ * γ) + u / (u * u + γ * γ) := by
      have he : u / (u * u + γ * γ) + u / (u * u + γ * γ) = (2 * u) / (u * u + γ * γ) := by
        ring
      rw [he, div_le_div_iff₀ hu0 hden]
      linarith only [hγsq]
    have hstep2 : (8 / 5) * ℓ / (2 * δ + c) ≤ (8 / 5) / u := by
      rw [div_le_div_iff₀ hd hu0]
      linarith only [hu2]
    linarith only [hstep, hstep2]
  exact arith2bc δ ℓ c K (u / (u * u + γ * γ) + u / (u * u + γ * γ)) hδ hℓ0 hK hKδ hc0 hc
    hlow2 hbound

/-- Two real zeros (counted with multiplicity) in the region are impossible for a real
non-principal character. -/
private lemma case_real_two
    (c₀ cZ δ c K : ℝ) (hc₀ : 0 ≤ c₀) (hcZ : 0 < cZ)
    (hδ : 0 < δ) (hδ8 : δ ≤ Real.log 2 / 8) (hc0 : 0 < c) (hc : c ≤ δ / 8)
    (hK : 0 ≤ K) (hKδ : K * δ ≤ 1 / 20) (hKbig : c₀ / Real.log 2 + cZ ≤ K)
    (Htriv : TrivBound c₀) (Hzeros : ZerosBound cZ)
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (hsq : χ ^ 2 = 1)
    (ρ₁ ρ₂ : ℂ) (him₁ : ρ₁.im = 0) (him₂ : ρ₂.im = 0)
    (hreg₁ : Davenport.InRegion c q ρ₁) (hreg₂ : Davenport.InRegion c q ρ₂)
    (hz₁ : DirichletCharacter.LFunction χ ρ₁ = 0) (hz₂ : DirichletCharacter.LFunction χ ρ₂ = 0)
    (hcount : ∀ x : ℂ, ((({ρ₁, ρ₂} : Multiset ℂ)).count x : ℕ∞)
      ≤ analyticOrderAt (DirichletCharacter.LFunction χ) x) : False := by
  have hl2pos : (0 : ℝ) < Real.log 2 := log_two_pos'
  obtain ⟨ℓ, hℓ⟩ : ∃ x : ℝ, Real.log ((q : ℝ) * (0 + 2)) = x := ⟨_, rfl⟩
  have hℓ2 : Real.log 2 ≤ ℓ := by
    rw [← hℓ]; have h := log_two_le_p1 q 0; rwa [abs_zero] at h
  have hℓ0 : 0 < ℓ := lt_of_lt_of_le hl2pos hℓ2
  obtain ⟨p, hp⟩ : ∃ x : ℝ, 2 * δ / ℓ = x := ⟨_, rfl⟩
  have hp0 : 0 < p := hp ▸ div_pos (by linarith only [hδ]) hℓ0
  have hp4 : p ≤ 1 / 4 := by
    rw [← hp, div_le_div_iff₀ hℓ0 (by norm_num)]; linarith only [hδ8, hℓ2]
  have hpℓ : p * ℓ = 2 * δ := by rw [← hp]; field_simp
  obtain ⟨σ, hσ⟩ : ∃ x : ℝ, x = 1 + p := ⟨_, rfl⟩
  have hσ1 : 1 < σ := by rw [hσ]; linarith only [hp0]
  have hσ2 : σ ≤ 2 := by rw [hσ]; linarith only [hp4]
  have hσm1 : σ - 1 = 2 * δ / ℓ := by rw [hσ, hp]; ring
  -- data attached to a real zero in the region
  have hstep : ∀ r : ℂ, r.im = 0 → Davenport.InRegion c q r →
      DirichletCharacter.LFunction χ r = 0 →
      ∃ v : ℝ, 0 < v ∧ v ≤ 17 / 64 ∧ v * ℓ ≤ 2 * δ + c ∧ (σ : ℂ) - r = ((v : ℝ) : ℂ) := by
    intro r hrim hrreg hrzero
    have hrre : r.re < 1 := by
      by_contra h
      exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
        (not_lt.mp h)) hrzero
    have hrreg' : 1 - c / ℓ ≤ r.re := by
      have h := hrreg
      simp only [Davenport.InRegion, Davenport.regionBoundary] at h
      rw [hrim, abs_zero, hℓ] at h
      exact h
    refine ⟨σ - r.re, by linarith only [hσ1, hrre], ?_, ?_, ?_⟩
    · have hbc : (1 - r.re) * ℓ ≤ c := by
        have h1 : 1 - r.re ≤ c / ℓ := by linarith only [hrreg']
        have h2 := mul_le_mul_of_nonneg_right h1 hℓ0.le
        rwa [div_mul_cancel₀ _ (ne_of_gt hℓ0)] at h2
      have hul : (σ - r.re) * ℓ = 2 * δ + (1 - r.re) * ℓ := by rw [hσ, ← hpℓ]; ring
      have h2 : (σ - r.re) * Real.log 2 ≤ (σ - r.re) * ℓ :=
        mul_le_mul_of_nonneg_left hℓ2 (by linarith only [hσ1, hrre])
      have h3 : (σ - r.re) * Real.log 2 ≤ (17 / 64) * Real.log 2 := by
        linarith only [h2, hul, hbc, hδ8, hc]
      exact le_of_mul_le_mul_right h3 hl2pos
    · have hbc : (1 - r.re) * ℓ ≤ c := by
        have h1 : 1 - r.re ≤ c / ℓ := by linarith only [hrreg']
        have h2 := mul_le_mul_of_nonneg_right h1 hℓ0.le
        rwa [div_mul_cancel₀ _ (ne_of_gt hℓ0)] at h2
      have hul : (σ - r.re) * ℓ = 2 * δ + (1 - r.re) * ℓ := by rw [hσ, ← hpℓ]; ring
      linarith only [hul, hbc]
    · apply Complex.ext
      · rw [Complex.sub_re, Complex.ofReal_re, Complex.ofReal_re]
      · rw [Complex.sub_im, Complex.ofReal_im, Complex.ofReal_im, hrim]; ring
  obtain ⟨u₁, hu₁0, hu₁s, hu₁2, hu₁e⟩ := hstep ρ₁ him₁ hreg₁ hz₁
  obtain ⟨u₂, hu₂0, hu₂s, hu₂2, hu₂e⟩ := hstep ρ₂ him₂ hreg₂ hz₂
  have hnorm : ∀ (r : ℂ) (v : ℝ), (σ : ℂ) - r = ((v : ℝ) : ℂ) → 0 < v → v ≤ 17 / 64 →
      ‖r - (σ : ℂ)‖ ≤ 1 / 2 := by
    intro r v hv hv0 hv1
    have hrs : r - (σ : ℂ) = ((-v : ℝ) : ℂ) := by
      have h : r - (σ : ℂ) = -((σ : ℂ) - r) := by ring
      rw [h, hv]; push_cast; ring
    rw [hrs, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg hv0.le]
    linarith only [hv1]
  have hinv : ∀ v : ℝ, ((1 : ℂ) / ((v : ℝ) : ℂ)).re = 1 / v := by
    intro v
    rw [show (1 : ℂ) / ((v : ℝ) : ℂ) = (((1 / v : ℝ)) : ℂ) by push_cast; ring]
    exact Complex.ofReal_re _
  have hbound := real_axis_bound c₀ cZ δ c K hc₀ hcZ hδ hK hKbig Htriv Hzeros q χ hχ hsq ℓ σ
    hℓ2 hℓ0 (le_of_eq hℓ) hσm1 hσ1 hσ2 ({ρ₁, ρ₂} : Multiset ℂ)
    (by
      intro x hx
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact hnorm x u₁ hu₁e hu₁0 hu₁s
      · exact hnorm x u₂ hu₂e hu₂0 hu₂s)
    hcount
  have hsum : (({ρ₁, ρ₂} : Multiset ℂ).map fun r => ((1 : ℂ) / ((σ : ℂ) - r)).re).sum
      = 1 / u₁ + 1 / u₂ := by
    simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.sum_cons,
      Multiset.map_singleton, Multiset.sum_singleton, hu₁e, hu₂e, hinv]
  rw [hsum] at hbound
  have hd : (0 : ℝ) < 2 * δ + c := by linarith only [hδ, hc0]
  have hb1 : ℓ / (2 * δ + c) ≤ 1 / u₁ := by
    rw [div_le_div_iff₀ hd hu₁0]; linarith only [hu₁2]
  have hb2 : ℓ / (2 * δ + c) ≤ 1 / u₂ := by
    rw [div_le_div_iff₀ hd hu₂0]; linarith only [hu₂2]
  have hX : (0 : ℝ) ≤ ℓ / (2 * δ + c) := le_of_lt (div_pos hℓ0 hd)
  have hlow2 : (8 / 5) * ℓ / (2 * δ + c) ≤ 1 / u₁ + 1 / u₂ := by
    rw [show (8 / 5 : ℝ) * ℓ / (2 * δ + c) = (8 / 5) * (ℓ / (2 * δ + c)) by ring]
    linarith only [hb1, hb2, hX]
  exact arith2bc δ ℓ c K (1 / u₁ + 1 / u₂) hδ hℓ0 hK hKδ hc0 hc hlow2 hbound

/-! ### The principal character -/

private lemma re_pos_of_region (c : ℝ) (hc0 : 0 < c) (hclog : c < Real.log 2)
    (q : ℕ) [NeZero q] (s : ℂ) (hreg : Davenport.InRegion c q s) : 0 < s.re := by
  have hl2 : (0 : ℝ) < Real.log 2 := log_two_pos'
  have hℓ2 : Real.log 2 ≤ Real.log ((q : ℝ) * (|s.im| + 2)) := log_two_le_p1 q s.im
  have h := hreg
  simp only [Davenport.InRegion, Davenport.regionBoundary] at h
  have hdiv : c / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ c / Real.log 2 :=
    div_le_div_of_nonneg_left hc0.le hl2 hℓ2
  have hlt : c / Real.log 2 < 1 := by rw [div_lt_one hl2]; exact hclog
  linarith only [h, hdiv, hlt]

private lemma one_sub_cpow_ne_zero (p : ℕ) (hp : 2 ≤ p) (s : ℂ) (hs : 0 < s.re) :
    (1 : ℂ) - (p : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 : (p : ℂ) ^ (-s) = 1 := by linear_combination -h
  have h2 : ‖((p : ℂ) ^ (-s))‖ = 1 := by rw [h1]; simp
  rw [Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re] at h2
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    have : (1 : ℕ) < p := by omega
    exact_mod_cast this
  have h3 := Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith only [hs] : -s.re < 0)
  linarith only [h2, h3]

private lemma case_principal (cζ c : ℝ) (hcζ : 0 < cζ) (hc0 : 0 < c) (hcle : c ≤ cζ)
    (hclog : c < Real.log 2)
    (Hzeta : ∀ s : ℂ, s ≠ 1 → 1 - cζ / Real.log (|s.im| + 2) ≤ s.re → riemannZeta s ≠ 0)
    (q : ℕ) [NeZero q] (s : ℂ) (hs1 : s ≠ 1) (hreg : Davenport.InRegion c q s) :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) s ≠ 0 := by
  have hl2 : (0 : ℝ) < Real.log 2 := log_two_pos'
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have habs := abs_nonneg s.im
  have ha2 : Real.log 2 ≤ Real.log (|s.im| + 2) :=
    Real.log_le_log (by norm_num) (by linarith only [habs])
  have ha0 : 0 < Real.log (|s.im| + 2) := lt_of_lt_of_le hl2 ha2
  have hℓ2 : Real.log 2 ≤ Real.log ((q : ℝ) * (|s.im| + 2)) := log_two_le_p1 q s.im
  have hℓ0 : 0 < Real.log ((q : ℝ) * (|s.im| + 2)) := lt_of_lt_of_le hl2 hℓ2
  have haℓ : Real.log (|s.im| + 2) ≤ Real.log ((q : ℝ) * (|s.im| + 2)) :=
    Real.log_le_log (by linarith only [habs]) (by nlinarith [habs, hq1])
  have hsre : 0 < s.re := re_pos_of_region c hc0 hclog q s hreg
  have hζ : riemannZeta s ≠ 0 := by
    refine Hzeta s hs1 ?_
    have hreg' : 1 - c / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ s.re := hreg
    have step1 : c / Real.log ((q : ℝ) * (|s.im| + 2))
        ≤ cζ / Real.log ((q : ℝ) * (|s.im| + 2)) := by gcongr
    have step2 : cζ / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ cζ / Real.log (|s.im| + 2) :=
      div_le_div_of_nonneg_left hcζ.le ha0 haℓ
    linarith only [hreg', step1, step2]
  show DirichletCharacter.LFunctionTrivChar q s ≠ 0
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hs1]
  refine mul_ne_zero ?_ hζ
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  exact one_sub_cpow_ne_zero p (Nat.prime_of_mem_primeFactors hp).two_le s hsre

end Sol

theorem _root_.SWPort.Davenport.zero_free_region_oai :
    ∃ c : ℝ, 0 < c ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        ∃ E : Set ℂ, Davenport.IsExceptionalSet c χ E ∧
          ∀ z ∈ E, deriv (DirichletCharacter.LFunction χ) z ≠ 0 := by
  obtain ⟨c₀', Htriv'⟩ := Davenport.neg_logDeriv_trivChar_le
  obtain ⟨cP, hcP, Hpole⟩ := Davenport.neg_logDeriv_trivChar_le_pole
  obtain ⟨cZ, hcZ, Hzeros⟩ := Davenport.neg_logDeriv_LFunction_le_sum_zeros
  obtain ⟨cζ, hcζ, Hzeta⟩ := Davenport.zeta_zero_free_region
  have hl2 : (0 : ℝ) < Real.log 2 := Sol.log_two_pos'
  -- normalise the first constant to be nonnegative
  obtain ⟨c₀, hc₀def⟩ : ∃ x : ℝ, max c₀' 0 = x := ⟨_, rfl⟩
  have hc₀ : 0 ≤ c₀ := hc₀def ▸ le_max_right _ _
  have hc₀' : c₀' ≤ c₀ := hc₀def ▸ le_max_left _ _
  have Htriv : Sol.TrivBound c₀ := by
    intro q _ σ h1 h2
    linarith only [Htriv' q σ h1 h2, hc₀']
  have hq0 : 0 ≤ c₀ / Real.log 2 := div_nonneg hc₀ hl2.le
  -- the master constant `K`
  obtain ⟨K, hKdef⟩ : ∃ x : ℝ, 6 * (c₀ / Real.log 2 + cZ + cP) = x := ⟨_, rfl⟩
  have hK : 0 ≤ K := by rw [← hKdef]; linarith only [hq0, hcZ, hcP]
  have hKbig1 : 3 * c₀ / Real.log 2 + 6 * cZ ≤ K := by
    rw [← hKdef]; rw [mul_div_assoc]; linarith only [hq0, hcZ, hcP]
  have hKbig2 : 3 * c₀ / Real.log 2 + 4 * cZ + 2 * cP ≤ K := by
    rw [← hKdef]; rw [mul_div_assoc]; linarith only [hq0, hcZ, hcP]
  have hKbig3 : c₀ / Real.log 2 + cZ ≤ K := by
    rw [← hKdef]; linarith only [hq0, hcZ, hcP]
  -- the small parameter `δ`
  obtain ⟨δ, hδdef⟩ : ∃ x : ℝ, min (Real.log 2 / 8) (1 / (20 * (K + 1))) = x := ⟨_, rfl⟩
  have hδ : 0 < δ := by
    rw [← hδdef]
    exact lt_min (by linarith only [hl2]) (by positivity)
  have hδ8 : δ ≤ Real.log 2 / 8 := hδdef ▸ min_le_left _ _
  have hKδ : K * δ ≤ 1 / 20 := by
    have h1 : δ ≤ 1 / (20 * (K + 1)) := hδdef ▸ min_le_right _ _
    have h2 : K * δ ≤ K * (1 / (20 * (K + 1))) := mul_le_mul_of_nonneg_left h1 hK
    have h3 : K * (1 / (20 * (K + 1))) ≤ 1 / 20 := by
      rw [mul_one_div, div_le_div_iff₀ (by linarith only [hK]) (by norm_num)]
      linarith only [hK]
    linarith only [h2, h3]
  -- the region constant `c`
  obtain ⟨c, hcdef⟩ : ∃ x : ℝ, min (δ / 8) cζ = x := ⟨_, rfl⟩
  have hc0 : 0 < c := by
    rw [← hcdef]; exact lt_min (by linarith only [hδ]) hcζ
  have hc : c ≤ δ / 8 := hcdef ▸ min_le_left _ _
  have hcle : c ≤ cζ := hcdef ▸ min_le_right _ _
  have hclog : c < Real.log 2 := by linarith only [hc, hδ8, hl2]
  refine ⟨c, hc0, ?_⟩
  intro q _ χ
  by_cases hχ1 : χ = 1
  · subst hχ1
    exact ⟨∅, ⟨Set.subsingleton_empty, by simp, fun s hs1 hreg _ =>
      Sol.case_principal cζ c hcζ hc0 hcle hclog Hzeta q s hs1 hreg⟩, by simp⟩
  by_cases hq2 : χ ^ 2 = 1
  · -- real (quadratic) non-principal character
    have hquad : χ.IsQuadratic := MulChar.isQuadratic_iff_sq_eq_one.mpr hq2
    refine ⟨{z : ℂ | z.im = 0 ∧ 0 < z.re ∧ z.re < 1 ∧ Davenport.InRegion c q z ∧
      DirichletCharacter.LFunction χ z = 0}, ⟨?_, ?_, ?_⟩, ?_⟩
    · -- at most one element
      rintro z₁ ⟨him₁, -, -, hreg₁, hz₁⟩ z₂ ⟨him₂, -, -, hreg₂, hz₂⟩
      by_contra hne
      refine Sol.case_real_two c₀ cZ δ c K hc₀ hcZ hδ hδ8 hc0 hc hK hKδ hKbig3 Htriv Hzeros
        q χ hχ1 hq2 z₁ z₂ him₁ him₂ hreg₁ hreg₂ hz₁ hz₂ ?_
      intro x
      by_cases hx1 : x = z₁
      · rw [hx1]
        have hcnt : ({z₁, z₂} : Multiset ℂ).count z₁ = 1 := by
          simp [Multiset.insert_eq_cons, Multiset.count_singleton, hne, Ne.symm hne, eq_comm]
        rw [hcnt]
        exact_mod_cast Sol.one_le_order_p0 hχ1 hz₁
      · by_cases hx2 : x = z₂
        · rw [hx2]
          have hcnt : ({z₁, z₂} : Multiset ℂ).count z₂ = 1 := by
            simp [Multiset.insert_eq_cons, Multiset.count_singleton, hne, Ne.symm hne, eq_comm]
          rw [hcnt]
          exact_mod_cast Sol.one_le_order_p0 hχ1 hz₂
        · have hcnt : ({z₁, z₂} : Multiset ℂ).count x = 0 := by
            simp [Multiset.insert_eq_cons, Multiset.count_singleton, hx1, hx2, eq_comm]
          rw [hcnt]; simp
    · -- description of the elements
      rintro z ⟨him, hre0, hre1, hreg, hz⟩
      exact ⟨him, hre0, hre1, hreg, hz, hquad, hχ1⟩
    · -- non-vanishing off the exceptional set
      intro s hs1 hreg hsE hzero
      apply hsE
      have hsre1 : s.re < 1 := by
        by_contra h
        exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ1)
          (not_lt.mp h)) hzero
      have hsre0 : 0 < s.re := Sol.re_pos_of_region c hc0 hclog q s hreg
      have him : s.im = 0 := by
        by_contra him
        by_cases hh : δ / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ |s.im|
        · exact Sol.case_real_high c₀ cZ cP δ c K hc₀ hcZ hcP hδ hδ8 hc0 hc hK hKδ hKbig2
            Htriv Hpole Hzeros q χ hχ1 hq2 s hreg hzero hh
        · exact Sol.case_real_low c₀ cZ δ c K hc₀ hcZ hδ hδ8 hc0 hc hK hKδ hKbig3
            Htriv Hzeros q χ hχ1 hquad s hreg hzero him (le_of_lt (not_le.mp hh))
      exact ⟨him, hsre0, hsre1, hreg, hzero⟩
    · -- the exceptional zero is simple
      rintro z ⟨him, -, -, hreg, hz⟩ hderiv
      refine Sol.case_real_two c₀ cZ δ c K hc₀ hcZ hδ hδ8 hc0 hc hK hKδ hKbig3 Htriv Hzeros
        q χ hχ1 hq2 z z him him hreg hreg hz hz ?_
      intro x
      by_cases hx : x = z
      · rw [hx]
        have hcnt : ({z, z} : Multiset ℂ).count z = 2 := by
          simp [Multiset.insert_eq_cons]
        rw [hcnt]
        exact_mod_cast Sol.two_le_order hχ1 hz hderiv
      · have hcnt : ({z, z} : Multiset ℂ).count x = 0 := by
          simp [Multiset.insert_eq_cons, hx]
        rw [hcnt]; simp
  · -- complex character
    exact ⟨∅, ⟨Set.subsingleton_empty, by simp, fun s _ hreg _ hzero =>
      Sol.case_complex c₀ cZ δ c K hc₀ hcZ hδ hδ8 hc0 hc hK hKδ hKbig1 Htriv Hzeros
        q χ hχ1 hq2 s hreg hzero⟩, by simp⟩

end SWPort
end

theorem solution : type_of% @SWPort.Davenport.zero_free_region_oai := @SWPort.Davenport.zero_free_region_oai
