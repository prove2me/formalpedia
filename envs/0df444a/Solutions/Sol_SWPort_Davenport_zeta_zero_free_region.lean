-- Prove2me | solution 1 for SWPort.Davenport.zeta_zero_free_region
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-08T19:24:50.002269+00:00
-- url     : https://prove2.me/submissions/dc0549e1-d469-4a08-a0a3-ec60c0d1b76e

import Mathlib
import Batteries.Tactic.Lemma
import Definitions.Def_SWPort_001

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
-- module Solutions.Artin.SW.Thm.Zeta23_WeilEF_zeta_logDeriv_partial_fraction
alias SWPort.Zeta23.WeilEF.zeta_logDeriv_partial_fraction := SWPort.Z.Zeta23.WeilEF.zeta_logDeriv_partial_fraction
end

section
-- module Solutions.Artin.SW.Thm.ZetaCont
namespace SWPort
/-! Ported from prove2.me: `ZetaCont` (98a55489-b0d8-434a-adb7-a97bcae5bec5, statement by Community (Bot)); proof = accepted direct submission 6c0ae475-e1dc-404f-a930-244a50218848 by Community (Bot). -/

































set_option lang.lemmaCmd true

open Complex Topology Filter Interval Set Asymptotics

local notation "ζ" => riemannZeta
local notation "ζ'" => deriv riemannZeta

-- Main theorem: if functions agree on a punctured set, their derivatives agree there too

/- New two theorems to be proven -/

-- Alternative cleaner proof using more direct approach

/- The set should be open so that f'(p) = O(1) for all p ∈ U -/

/-- We use `ζ` to denote the Rieman zeta function and `ζ₀` to denote the alternative Rieman zeta
function. -/
local notation "ζ₀" => riemannZeta0

-- move near `Real.differentiableAt_rpow_const_of_ne`

-- MOVE TO MATHLIB near `differentiableAt_riemannZeta`

-- **Another AlphaProof collaboration (thanks to Thomas Hubert!)**

-- **End collaboration 6/20/25**

/-% ** Bad delimiters on purpose **
Annoying: we have reciprocals of $log |t|$ in the bounds, and we've assumed that $|t|>3$; but we
want to make things uniform in $t$. Let's change to things like $log (|t|+3)$ instead of $log |t|$.
\begin{lemma}[LogLeLog]\label{LogLeLog}\lean{LogLeLog}\leanok
There is a constant $C>0$ so that for all $t>3$,
$$
1/\log t \le C / \log (t + 3).
$$
\end{lemma}
%-/
/-%
\begin{proof}
Write
$$
\log (t + 3) = \log t + \log (1 + 3/t) = \log t + O(1/t).
$$
Then we can bound $1/\log t$ by $C / \log (t + 3)$ for some constant $C>0$.
\end{proof}
%-/

-- **Begin collaboration with the Alpha Proof team! 5/29/25**

theorem _root_.SWPort.ZetaCont : ContinuousOn ζ (univ \ {1}) := by
  apply continuousOn_of_forall_continuousAt (fun x hx ↦ ?_)
  apply DifferentiableAt.continuousAt (𝕜 := ℂ)
  convert differentiableAt_riemannZeta ?_
  simp only [mem_diff, mem_univ, mem_singleton_iff, true_and] at hx
  exact hx

-- **End collaboration**

open ArithmeticFunction (vonMangoldt)
local notation "Λ" => vonMangoldt
--TODO generalize to any LSeries with nonnegative coefficients

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.ZetaNoZerosInBox
namespace SWPort
/-! Ported from prove2.me: `ZetaNoZerosInBox` (4c2de89c-3452-484a-be29-28cd1efa0e0f, statement by Community (Bot)); proof = accepted sketch submission 32105771-e3e8-4f0f-bc2b-dfee0df9f18f by Community (Bot). -/


































set_option lang.lemmaCmd true

open Complex Topology Filter Interval Set Asymptotics

local notation "ζ" => riemannZeta
local notation "ζ'" => deriv riemannZeta

-- Main theorem: if functions agree on a punctured set, their derivatives agree there too

/- New two theorems to be proven -/

-- Alternative cleaner proof using more direct approach

/- The set should be open so that f'(p) = O(1) for all p ∈ U -/

/-- We use `ζ` to denote the Rieman zeta function and `ζ₀` to denote the alternative Rieman zeta
function. -/
local notation "ζ₀" => riemannZeta0

-- move near `Real.differentiableAt_rpow_const_of_ne`

-- MOVE TO MATHLIB near `differentiableAt_riemannZeta`

-- **Another AlphaProof collaboration (thanks to Thomas Hubert!)**

-- **End collaboration 6/20/25**

/-% ** Bad delimiters on purpose **
Annoying: we have reciprocals of $log |t|$ in the bounds, and we've assumed that $|t|>3$; but we
want to make things uniform in $t$. Let's change to things like $log (|t|+3)$ instead of $log |t|$.
\begin{lemma}[LogLeLog]\label{LogLeLog}\lean{LogLeLog}\leanok
There is a constant $C>0$ so that for all $t>3$,
$$
1/\log t \le C / \log (t + 3).
$$
\end{lemma}
%-/
/-%
\begin{proof}
Write
$$
\log (t + 3) = \log t + \log (1 + 3/t) = \log t + O(1/t).
$$
Then we can bound $1/\log t$ by $C / \log (t + 3)$ for some constant $C>0$.
\end{proof}
%-/

-- **Begin collaboration with the Alpha Proof team! 5/29/25**

theorem _root_.SWPort.ZetaNoZerosInBox (T : ℝ) :
    ∃ (σ : ℝ) (_ : σ < 1), ∀ (t : ℝ) (_ : |t| ≤ T)
    (σ' : ℝ) (_ : σ' ≥ σ), ζ (σ' + t * I) ≠ 0 := by
  by_contra! h
  have hn (n : ℕ) := h (1 - 1 / (n + 1)) (sub_lt_self _ (by positivity))

  have : ∃ (tn : ℕ → ℝ) (σn : ℕ → ℝ), (∀ n, σn n ≤ 1) ∧
    (∀ n, (1 : ℝ) - 1 / (n + 1) ≤ σn n) ∧ (∀ n, |tn n| ≤ T) ∧
    (∀ n, ζ (σn n + tn n * I) = 0) := by
    choose t ht σ' hσ' hζ using hn
    refine ⟨t, σ', ?_, hσ', ht, hζ⟩
    intro n
    by_contra! hσn
    have := riemannZeta_ne_zero_of_one_lt_re (s := σ' n + t n * I)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, ne_eq] at this
    exact this hσn (hζ n)

  choose t σ' hσ'_le hσ'_ge ht hζ using this

  have σTo1 : Filter.Tendsto σ' Filter.atTop (𝓝 1) := by
    use sub_zero (1: ℝ)▸tendsto_order.2 ⟨fun A B=>? _,fun A B=>?_⟩
    · apply (((tendsto_inv_atTop_nhds_zero_nat.comp
        (Filter.tendsto_add_atTop_nat (1))).congr (by norm_num)).const_sub 1).eventually_const_lt
          B|>.mono (hσ'_ge ·|>.trans_lt')
    · norm_num[(hσ'_le _).trans_lt, B.trans_le']

  have : ∃ (t₀ : ℝ) (subseq : ℕ → ℕ),
      Filter.Tendsto (t ∘ subseq) Filter.atTop (𝓝 t₀) ∧
      Filter.Tendsto subseq Filter.atTop Filter.atTop := by
    refine (isCompact_Icc.isSeqCompact fun and => abs_le.1 (ht and)).imp fun and ⟨x, A, B, _⟩ => ?_
    use A, by omega, B.tendsto_atTop

  obtain ⟨t₀, subseq, tTendsto, subseqTendsto⟩ := this

  have σTo1 : Filter.Tendsto (σ' ∘ subseq) Filter.atTop (𝓝 1) :=
    σTo1.comp subseqTendsto

  have (n : ℕ) : ζ (σ' (subseq n) + I * (t (subseq n))) = 0 := by
    convert hζ (subseq n) using 3
    ring

  have ToOneT0 : Filter.Tendsto (fun n ↦ (σ' (subseq n) : ℂ) + Complex.I * (t (subseq n))) Filter.atTop
      (𝓝[≠]((1 : ℂ) + I * t₀)) := by
    simp_rw [tendsto_nhdsWithin_iff, Function.comp_def] at tTendsto ⊢
    constructor
    · exact (σTo1.ofReal.add (tTendsto.ofReal.const_mul _)).trans (by simp)
    · filter_upwards with n
      apply ne_of_apply_ne ζ
      rw [this]
      apply Ne.symm
      apply riemannZeta_ne_zero_of_one_le_re
      simp only [add_re, one_re, mul_re, I_re, ofReal_re, zero_mul, I_im, ofReal_im, mul_zero,
        sub_self, add_zero, le_refl]

  by_cases ht₀ : t₀ = 0
  · have ZetaBlowsUp : ∀ᶠ s in 𝓝[≠](1 : ℂ), ‖ζ s‖ ≥ 1 := by
      simp_all only [ge_iff_le, one_div, tsub_le_iff_right, Function.comp_def, ofReal_zero,
        mul_zero, add_zero, norm_eq_sqrt_real_inner, Complex.inner, mul_re, conj_re, conj_im,
        mul_neg, sub_neg_eq_add, Real.one_le_sqrt, eventually_nhdsWithin_iff, mem_compl_iff,
        mem_singleton_iff]
      contrapose! h
      simp_all only [ne_eq]
      delta abs at*
      exfalso
      simp_rw [Metric.nhds_basis_ball.frequently_iff]at*
      choose! I A B using h
      choose a s using exists_seq_strictAnti_tendsto (0: ℝ)
      apply ((isCompact_closedBall _ _).isSeqCompact
        fun and=>(A _ (s.2.1 and)).le.trans (s.2.2.bddAbove_range.some_mem ⟨and, rfl⟩)).elim
      simp only [Metric.mem_ball, dist_eq_norm_sub] at A
      refine fun and ⟨a, H, S, M⟩=> ?_
      refine absurd (tendsto_nhds_unique M (tendsto_sub_nhds_zero_iff.1
        (( squeeze_zero_norm fun and=>le_of_lt (A _ (s.2.1 _) ) )
          (s.2.2.comp S.tendsto_atTop)))) fun and=>?_
      norm_num[*,Function.comp_def] at M
      have:=@riemannZeta_residue_one
      use one_ne_zero (tendsto_nhds_unique (this.comp (tendsto_nhdsWithin_iff.2
        ⟨ M,.of_forall (by norm_num[*])⟩)) ( squeeze_zero_norm ?_
          ((M.sub_const 1).norm.trans (by rw [sub_self,norm_zero]))))
      use fun and =>.trans (norm_mul_le_of_le ↑(le_rfl) (Complex.norm_def _▸Real.sqrt_le_one.mpr
        (B ↑_ (s.2.1 ↑_)).right.le)) (by rw [mul_one])

    have ZetaNonZ : ∀ᶠ s in 𝓝[≠](1 : ℂ), ζ s ≠ 0 := by
      filter_upwards [ZetaBlowsUp]
      intro s hs hfalse
      rw [hfalse] at hs
      simp only [norm_zero, ge_iff_le] at hs
      linarith

    rw [ht₀] at ToOneT0
    simp only [ofReal_zero, mul_zero, add_zero] at ToOneT0
    rcases (ToOneT0.eventually ZetaNonZ).exists with ⟨n, hn⟩
    exact hn (this n)

  · have zetaIsZero : ζ (1 + Complex.I * t₀) = 0 := by
      have cont := @ZetaCont
      use isClosed_singleton.isSeqClosed
        this
        (.comp
          (cont.continuousAt.comp (eventually_ne_nhds (by field_simp; simp [ht₀])).mono
            fun and=>.intro ⟨⟩)
          (ToOneT0.trans (inf_le_left)))

    exact riemannZeta_ne_zero_of_one_le_re (s := 1 + I * t₀) (by simp) zetaIsZero

-- **End collaboration**

open ArithmeticFunction (vonMangoldt)
local notation "Λ" => vonMangoldt
--TODO generalize to any LSeries with nonnegative coefficients

end SWPort
end

section
-- module Solutions.Artin.SW.Thm.Davenport_zeta_zero_free_region
namespace SWPort
/-! Ported from prove2.me: `Davenport.zeta_zero_free_region` (0dba2dc9-e9a0-442a-ad71-dc6eefb8c001, statement by alya); proof = accepted sketch submission 4c05d6ff-50fe-4193-9977-f98fe6f65d93 by alya. -/











/-!
# The de la Vallée Poussin zero-free region for `ζ`

We prove `∃ c > 0, ∀ s ≠ 1, 1 - c/log(|Im s|+2) ≤ Re s → ζ s ≠ 0`.

Bounded heights (`|Im s| ≤ 6`) are handled by the platform theorem `ZetaNoZerosInBox`.
For `|Im s| > 6` we run the classical `3`-`4`-`1` argument: `Davenport.logDeriv_three_four_one`
at modulus `q = 1` (where every Dirichlet `L`-function is `ζ`), together with

* `Davenport.neg_logDeriv_trivChar_le` for the term on the real axis,
* `Zeta23.WeilEF.zeta_logDeriv_partial_fraction` for the term at height `γ`, keeping the
  contribution `-Re 1/(s-ρ)` of the hypothetical zero `ρ`, and
* the same partial-fraction theorem, with the zero sum discarded, at height `2γ`.
-/

set_option linter.unusedVariables false

open Complex

namespace Sol

/-- `Re (1/w) ≥ 0` when `Re w > 0`. -/
private lemma inv_re_nonneg_p1 {w : ℂ} (h : 0 < w.re) : 0 ≤ (w⁻¹).re := by
  rw [Complex.inv_re]
  exact div_nonneg h.le (Complex.normSq_nonneg _)

/-- A zero of `ζ` has real part `< 1`. -/
private lemma zero_re_lt_one_p1 {ρ : ℂ} (h : riemannZeta ρ = 0) : ρ.re < 1 := by
  by_contra hc
  exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp hc) h

/-- Large-height bound: `-Re ζ'/ζ(s) ≤ C log(|t|+3)` for `1 < σ ≤ 2`, `|t| ≥ 6`. -/
private lemma zeta_high_p1 :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 1 < s.re → s.re ≤ 2 → 6 ≤ |s.im| →
      (-(deriv riemannZeta s / riemannZeta s)).re ≤ C * Real.log (|s.im| + 3) := by
  obtain ⟨C, hC, H⟩ := Zeta23.WeilEF.zeta_logDeriv_partial_fraction
  refine ⟨C, hC, fun s h1 h2 h6 => ?_⟩
  obtain ⟨Z, hZset, -, hZbnd⟩ := H s.im h6
  have hball : s ∈ Metric.closedBall (2 + (s.im : ℂ) * I) (3/2) := by
    have he : s - (2 + (s.im : ℂ) * I) = ((s.re - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [Metric.mem_closedBall, Complex.dist_eq, he, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    linarith
  have hsz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (le_of_lt h1)
  have key := hZbnd s hball hsz
  -- the zero sum has nonnegative real part
  have hsum : 0 ≤ (∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)).re := by
    rw [Complex.re_sum]
    refine Finset.sum_nonneg fun ρ hρ => ?_
    have hρ0 : riemannZeta ρ = 0 := by
      have : ρ ∈ {ρ ∈ Metric.closedBall (2 + (s.im : ℂ) * I) (22/25 * (91/50)) |
          riemannZeta ρ = 0} := by rw [← hZset]; exact_mod_cast hρ
      exact this.2
    have hre : 0 < (s - ρ).re := by
      have := zero_re_lt_one_p1 hρ0
      simp only [Complex.sub_re]
      linarith
    have : ((analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)).re
        = (analyticOrderNatAt riemannZeta ρ : ℝ) * ((s - ρ)⁻¹).re := by
      rw [div_eq_mul_inv]
      simp [Complex.mul_re]
    rw [this]
    exact mul_nonneg (Nat.cast_nonneg _) (inv_re_nonneg_p1 hre)
  have habs : |(logDeriv riemannZeta s
      - ∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)).re|
      ≤ C * Real.log (|s.im| + 3) := (Complex.abs_re_le_norm _).trans key
  have h := abs_le.mp habs
  rw [Complex.sub_re] at h
  rw [show (-(deriv riemannZeta s / riemannZeta s)) = -(logDeriv riemannZeta s) by
    rw [logDeriv_apply], Complex.neg_re]
  linarith [h.1, hsum]

private lemma log_two_le_p2 (t : ℝ) : Real.log 2 ≤ Real.log (|t| + 2) :=
  Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])

private lemma log_two_pos_p1 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)

private lemma log_three_le_p1 (t : ℝ) : Real.log (|t| + 3) ≤ 2 * Real.log (|t| + 2) := by
  have h0 := abs_nonneg t
  have h1 : |t| + 3 ≤ (|t| + 2) ^ 2 := by nlinarith
  have h2 : Real.log (|t| + 3) ≤ Real.log ((|t| + 2) ^ 2) :=
    Real.log_le_log (by linarith) h1
  rwa [Real.log_pow] at h2
  

/-- A zero of `ζ` other than the pole has positive analytic order. -/
private lemma one_le_order_p1 {ρ : ℂ} (hρ1 : ρ ≠ 1) (h0 : riemannZeta ρ = 0) :
    1 ≤ analyticOrderNatAt riemannZeta ρ := by
  have hmem : ρ ∈ ({(1:ℂ)}ᶜ : Set ℂ) := hρ1
  have hA : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ hmem
  have hne0 : analyticOrderAt riemannZeta ρ ≠ 0 := hA.analyticOrderAt_ne_zero.mpr h0
  have hnetop : analyticOrderAt riemannZeta ρ ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    have hU : IsPreconnected ({(1:ℂ)}ᶜ : Set ℂ) :=
      (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
    have heq := analyticOn_riemannZeta.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU hmem htop
    have h2 : riemannZeta 2 = 0 := heq (by simp)
    exact riemannZeta_ne_zero_of_one_le_re (by norm_num) h2
  rw [Nat.one_le_iff_ne_zero]
  simp only [analyticOrderNatAt, ne_eq, ENat.toNat_eq_zero]
  tauto

/-- Partial-fraction bound keeping one zero. -/
private lemma zeta_zero_sum :
    ∃ C : ℝ, 0 < C ∧ ∀ (s ρ : ℂ), 1 < s.re → s.re ≤ 2 → 6 ≤ |s.im| →
      riemannZeta ρ = 0 → ‖ρ - (2 + (s.im : ℂ) * I)‖ ≤ 22/25 * (91/50) →
        (-(deriv riemannZeta s / riemannZeta s)).re
          ≤ C * Real.log (|s.im| + 3) - ((1:ℂ) / (s - ρ)).re := by
  obtain ⟨C, hC, H⟩ := Zeta23.WeilEF.zeta_logDeriv_partial_fraction
  refine ⟨C, hC, fun s ρ h1 h2 h6 hρ0 hρball => ?_⟩
  obtain ⟨Z, hZset, -, hZbnd⟩ := H s.im h6
  have hball : s ∈ Metric.closedBall (2 + (s.im : ℂ) * I) (3/2) := by
    have he : s - (2 + (s.im : ℂ) * I) = ((s.re - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [Metric.mem_closedBall, Complex.dist_eq, he, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    linarith
  have hsz : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_le_re (le_of_lt h1)
  have key := hZbnd s hball hsz
  -- membership of `ρ` in `Z`
  have hρZ : ρ ∈ Z := by
    have : ρ ∈ {ρ ∈ Metric.closedBall (2 + (s.im : ℂ) * I) (22/25 * (91/50)) |
        riemannZeta ρ = 0} := by
      refine ⟨?_, hρ0⟩
      rw [Metric.mem_closedBall, Complex.dist_eq]
      exact hρball
    rw [← hZset] at this
    exact_mod_cast this
  -- every term is nonnegative, and the `ρ`-term dominates `Re 1/(s-ρ)`
  have hterm : ∀ r ∈ Z, 0 ≤ ((analyticOrderNatAt riemannZeta r : ℂ) / (s - r)).re := by
    intro r hr
    have hr0 : riemannZeta r = 0 := by
      have : r ∈ {r ∈ Metric.closedBall (2 + (s.im : ℂ) * I) (22/25 * (91/50)) |
          riemannZeta r = 0} := by rw [← hZset]; exact_mod_cast hr
      exact this.2
    have hre : 0 < (s - r).re := by
      have := zero_re_lt_one_p1 hr0
      simp only [Complex.sub_re]; linarith
    have he : ((analyticOrderNatAt riemannZeta r : ℂ) / (s - r)).re
        = (analyticOrderNatAt riemannZeta r : ℝ) * ((s - r)⁻¹).re := by
      rw [div_eq_mul_inv]; simp [Complex.mul_re]
    rw [he]
    exact mul_nonneg (Nat.cast_nonneg _) (inv_re_nonneg_p1 hre)
  have hρ1 : ρ ≠ 1 := by
    intro h
    rw [h] at hρ0
    exact riemannZeta_ne_zero_of_one_le_re (by norm_num) hρ0
  have hreρ : 0 < (s - ρ).re := by
    have := zero_re_lt_one_p1 hρ0
    simp only [Complex.sub_re]; linarith
  have hbig : ((1:ℂ) / (s - ρ)).re
      ≤ (∑ r ∈ Z, (analyticOrderNatAt riemannZeta r : ℂ) / (s - r)).re := by
    rw [Complex.re_sum]
    refine le_trans ?_ (Finset.single_le_sum hterm hρZ)
    have he : ((analyticOrderNatAt riemannZeta ρ : ℂ) / (s - ρ)).re
        = (analyticOrderNatAt riemannZeta ρ : ℝ) * ((s - ρ)⁻¹).re := by
      rw [div_eq_mul_inv]; simp [Complex.mul_re]
    rw [he, one_div]
    have h1le : (1:ℝ) ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) := by
      exact_mod_cast one_le_order_p1 hρ1 hρ0
    nlinarith [inv_re_nonneg_p1 hreρ, h1le]
  have habs : |(logDeriv riemannZeta s
      - ∑ r ∈ Z, (analyticOrderNatAt riemannZeta r : ℂ) / (s - r)).re|
      ≤ C * Real.log (|s.im| + 3) := (Complex.abs_re_le_norm _).trans key
  have h := abs_le.mp habs
  rw [Complex.sub_re] at h
  rw [show (-(deriv riemannZeta s / riemannZeta s)) = -(logDeriv riemannZeta s) by
    rw [logDeriv_apply], Complex.neg_re]
  linarith [h.1, hbig]

/-- The real-arithmetic contradiction behind the de la Vallée Poussin argument. -/
private lemma arith1_p1 (δ ℓ u c K : ℝ) (hδ : 0 < δ) (hℓ : 0 < ℓ) (hu : 0 < u)
    (hK : 0 ≤ K) (hKδ : K * δ ≤ 1 / 2) (hc0 : 0 < c) (hc : c ≤ δ / 8)
    (h1 : 4 * (1 / u) ≤ 3 * (ℓ / δ) + K * ℓ) (h2 : u * ℓ ≤ δ + c) : False := by
  have hul : 0 < u * ℓ := mul_pos hu hℓ
  have h4 : (4 : ℝ) / u ≤ 3 * (ℓ / δ) + K * ℓ := by
    rw [div_eq_mul_inv, ← one_div]; linarith
  rw [div_le_iff₀ hu] at h4
  have hkey : 4 * δ ≤ (u * ℓ) * (3 + K * δ) := by
    have h5 := mul_le_mul_of_nonneg_right h4 hδ.le
    have h6 : (3 * (ℓ / δ) + K * ℓ) * u * δ = (u * ℓ) * (3 + K * δ) := by field_simp
    linarith [h5, h6.le, h6.ge]
  nlinarith [hkey, h2, hKδ, hc, hδ, hul, hc0]


end Sol

open Sol in
theorem _root_.SWPort.Davenport.zeta_zero_free_region_oai : ∃ c : ℝ, 0 < c ∧
    ∀ s : ℂ, s ≠ 1 → 1 - c / Real.log (|s.im| + 2) ≤ s.re → riemannZeta s ≠ 0 := by
  obtain ⟨Ch, hCh, Hh⟩ := zeta_high_p1
  obtain ⟨Cz, hCz, Hz⟩ := zeta_zero_sum
  obtain ⟨c₀', Htriv'⟩ := Davenport.neg_logDeriv_trivChar_le
  obtain ⟨σ₀, hσ₀, Hbox⟩ := ZetaNoZerosInBox 6
  have hl2 : (0:ℝ) < Real.log 2 := log_two_pos_p1
  have hl2' : (1:ℝ)/2 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  obtain ⟨c₀, hc₀def⟩ : ∃ x : ℝ, max c₀' 0 = x := ⟨_, rfl⟩
  have hc₀ : 0 ≤ c₀ := hc₀def ▸ le_max_right _ _
  have hc₀' : c₀' ≤ c₀ := hc₀def ▸ le_max_left _ _
  have Htriv : ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (-(deriv riemannZeta (σ:ℂ) / riemannZeta (σ:ℂ))).re ≤ 1 / (σ - 1) + c₀ := by
    intro σ ha hb
    have h := Htriv' 1 σ ha hb
    simp only [DirichletCharacter.LFunction_modOne_eq] at h
    linarith
  obtain ⟨K, hKdef⟩ : ∃ x : ℝ, 3 * c₀ / Real.log 2 + 4 * Cz + 2 * Ch = x := ⟨_, rfl⟩
  have hK : 0 ≤ K := by
    have h : 0 ≤ 3 * c₀ / Real.log 2 := by positivity
    rw [← hKdef]; linarith only [h, hCz.le, hCh.le]
  obtain ⟨δ, hδdef⟩ : ∃ x : ℝ, min (1/2) (1 / (2 * (K + 1))) = x := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [← hδdef]; exact lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1/2 := hδdef ▸ min_le_left _ _
  have hKδ : K * δ ≤ 1/2 := by
    have h1 : δ ≤ 1 / (2 * (K + 1)) := hδdef ▸ min_le_right _ _
    have h2 : K * δ ≤ K * (1 / (2 * (K + 1))) := mul_le_mul_of_nonneg_left h1 hK
    have h3 : K * (1 / (2 * (K + 1))) ≤ 1/2 := by
      rw [mul_one_div, div_le_div_iff₀ (by linarith only [hK]) (by norm_num)]
      linarith only [hK]
    linarith only [h2, h3]
  obtain ⟨c, hcdef⟩ : ∃ x : ℝ, min (δ/16) ((1 - σ₀) * Real.log 2) = x := ⟨_, rfl⟩
  have hc0 : 0 < c := by
    rw [← hcdef]
    exact lt_min (by linarith only [hδ0]) (by nlinarith only [hσ₀, hl2])
  have hcδ : c ≤ δ/16 := hcdef ▸ min_le_left _ _
  have hcσ : c ≤ (1 - σ₀) * Real.log 2 := hcdef ▸ min_le_right _ _
  refine ⟨c, hc0, fun s hs1 hreg hzero => ?_⟩
  obtain ⟨β, hβ⟩ : ∃ x : ℝ, s.re = x := ⟨_, rfl⟩
  obtain ⟨γ, hγ⟩ : ∃ x : ℝ, s.im = x := ⟨_, rfl⟩
  rw [hβ, hγ] at hreg
  have habs := abs_nonneg γ
  have hl2ℓ : Real.log 2 ≤ Real.log (|γ| + 2) := log_two_le_p2 γ
  have hℓ2pos : 0 < Real.log (|γ| + 2) := lt_of_lt_of_le hl2 hl2ℓ
  have hcℓ : c / Real.log (|γ| + 2) ≤ c / Real.log 2 :=
    div_le_div_of_nonneg_left hc0.le hl2 hl2ℓ
  rcases le_or_gt |γ| 6 with hlow | hhigh
  · -- bounded height: `ZetaNoZerosInBox`
    have hβσ₀ : σ₀ ≤ β := by
      have h1 : c / Real.log 2 ≤ 1 - σ₀ := by
        rw [div_le_iff₀ hl2]; linarith only [hcσ]
      linarith only [hreg, hcℓ, h1]
    have hbox := Hbox γ hlow β hβσ₀
    rw [← hβ, ← hγ, Complex.re_add_im s] at hbox
    exact hbox hzero
  · -- large height: the 3-4-1 argument
    have hβ1 : β < 1 := by rw [← hβ]; exact zero_re_lt_one_p1 hzero
    have h6 : (6:ℝ) ≤ |γ| := hhigh.le
    obtain ⟨L, hL⟩ : ∃ x : ℝ, Real.log (|γ| + 3) = x := ⟨_, rfl⟩
    have hLl2 : Real.log 2 ≤ L := by
      rw [← hL]; exact Real.log_le_log (by norm_num) (by linarith only [h6])
    have hL0 : 0 < L := lt_of_lt_of_le hl2 hLl2
    have hL2ℓ : L ≤ 2 * Real.log (|γ| + 2) := by rw [← hL]; exact log_three_le_p1 γ
    have hbc : (1 - β) * L ≤ δ/8 := by
      have h1 : 1 - β ≤ c / Real.log (|γ| + 2) := by linarith only [hreg]
      have h2 : (1 - β) * L ≤ (c / Real.log (|γ| + 2)) * L :=
        mul_le_mul_of_nonneg_right h1 hL0.le
      have h3 : (c / Real.log (|γ| + 2)) * L
          ≤ (c / Real.log (|γ| + 2)) * (2 * Real.log (|γ| + 2)) :=
        mul_le_mul_of_nonneg_left hL2ℓ (by positivity)
      have h4 : (c / Real.log (|γ| + 2)) * (2 * Real.log (|γ| + 2)) = 2 * c := by
        field_simp
      linarith only [h2, h3, h4.le, h4.ge, hcδ]
    have hβbig : (15:ℝ)/16 ≤ β := by
      have h1 : c / Real.log 2 ≤ 1/16 := by
        rw [div_le_iff₀ hl2]
        nlinarith only [hcδ, hδ1, hl2', hc0]
      linarith only [hreg, hcℓ, h1]
    obtain ⟨σ, hσ⟩ : ∃ x : ℝ, 1 + δ / L = x := ⟨_, rfl⟩
    have hδL : 0 < δ / L := div_pos hδ0 hL0
    have hσ1 : 1 < σ := by rw [← hσ]; linarith only [hδL]
    have hσ2 : σ ≤ 2 := by
      have h : δ / L ≤ 1 := by rw [div_le_one hL0]; linarith only [hδ1, hLl2, hl2']
      rw [← hσ]; linarith only [h]
    have hσm1 : σ - 1 = δ / L := by rw [← hσ]; ring
    obtain ⟨u, hu⟩ : ∃ x : ℝ, σ - β = x := ⟨_, rfl⟩
    have hu0 : 0 < u := by rw [← hu]; linarith only [hσ1, hβ1]
    have huL : u * L = δ + (1 - β) * L := by
      rw [← hu, ← hσ]; field_simp; ring
    have hu2 : u * L ≤ δ + δ/8 := by rw [huL]; linarith only [hbc]
    obtain ⟨w, hw⟩ : ∃ z : ℂ, (σ : ℂ) + (γ : ℂ) * I = z := ⟨_, rfl⟩
    have hwre : w.re = σ := by rw [← hw]; simp
    have hwim : w.im = γ := by rw [← hw]; simp
    obtain ⟨w₂, hw2⟩ : ∃ z : ℂ, (σ : ℂ) + 2 * (γ : ℂ) * I = z := ⟨_, rfl⟩
    have hw2re : w₂.re = σ := by rw [← hw2]; simp
    have hw2im : w₂.im = 2 * γ := by rw [← hw2]; simp
    have hws : w - s = ((u : ℝ) : ℂ) := by
      apply Complex.ext
      · rw [Complex.sub_re, hwre, hβ, ← hu, Complex.ofReal_re]
      · rw [Complex.sub_im, hwim, hγ, Complex.ofReal_im]; ring
    have hsw : ‖s - (2 + ((w.im : ℝ) : ℂ) * I)‖ ≤ 22/25 * (91/50) := by
      rw [hwim]
      have he : s - (2 + (γ : ℂ) * I) = ((β - 2 : ℝ) : ℂ) := by
        apply Complex.ext
        · rw [Complex.sub_re, hβ]; simp
        · rw [Complex.sub_im, hγ]; simp
      rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith only [hβ1])]
      linarith only [hβbig]
    have hB := Hz w s (by rw [hwre]; exact hσ1) (by rw [hwre]; exact hσ2)
      (by rw [hwim]; exact h6) hzero hsw
    rw [hwim, hL, hws] at hB
    have hinv : ((1:ℂ) / ((u : ℝ) : ℂ)).re = 1 / u := by
      rw [show (1:ℂ) / ((u:ℝ) : ℂ) = (((1/u : ℝ)) : ℂ) by push_cast; ring]
      exact Complex.ofReal_re _
    rw [hinv] at hB
    have hC := Hh w₂ (by rw [hw2re]; exact hσ1) (by rw [hw2re]; exact hσ2)
      (by rw [hw2im, abs_mul, abs_two]; linarith only [h6])
    rw [hw2im] at hC
    have hClog : Real.log (|2 * γ| + 3) ≤ 2 * L := by
      have h1 : |2 * γ| + 3 ≤ 2 * (|γ| + 3) := by
        rw [abs_mul, abs_two]; linarith only [habs]
      have h2 : Real.log (|2 * γ| + 3) ≤ Real.log (2 * (|γ| + 3)) :=
        Real.log_le_log (by positivity) h1
      rw [Real.log_mul (by norm_num) (by linarith only [habs]), hL] at h2
      linarith only [h2, hLl2]
    have hC' : (-(deriv riemannZeta w₂ / riemannZeta w₂)).re ≤ 2 * (Ch * L) := by
      have h := mul_le_mul_of_nonneg_left hClog hCh.le
      linarith only [hC, h]
    have hA := Htriv σ hσ1 hσ2
    rw [hσm1, one_div_div] at hA
    have h341 := Davenport.logDeriv_three_four_one 1 (1 : DirichletCharacter ℂ 1) σ γ hσ1
    simp only [DirichletCharacter.LFunction_modOne_eq] at h341
    rw [hw, hw2] at h341
    have hfin : 3 * c₀ + 4 * (Cz * L) + 2 * (Ch * L) ≤ K * L := by
      have h1 : 3 * c₀ ≤ (3 * c₀ / Real.log 2) * L := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hl2]
        exact mul_le_mul_of_nonneg_left hLl2 (by linarith only [hc₀])
      have h2 : K * L = (3 * c₀ / Real.log 2) * L + 4 * Cz * L + 2 * Ch * L := by
        rw [← hKdef]; ring
      linarith only [h1, h2]
    have hmain : 4 * (1 / u) ≤ 3 * (L / δ) + K * L := by
      linarith only [h341, hA, hB, hC', hfin]
    exact arith1_p1 δ L u (δ/8) K hδ0 hL0 hu0 hK hKδ (by linarith only [hδ0]) (le_refl _)
      hmain hu2

end SWPort
end

theorem solution : type_of% @SWPort.Davenport.zeta_zero_free_region_oai := @SWPort.Davenport.zeta_zero_free_region_oai
