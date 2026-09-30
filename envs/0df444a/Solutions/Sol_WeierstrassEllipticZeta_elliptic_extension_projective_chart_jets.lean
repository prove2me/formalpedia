-- Prove2me | solution 1 for WeierstrassEllipticZeta.elliptic_extension_projective_chart_jets
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T19:36:36.042799+00:00
-- url     : https://prove2.me/submissions/7c7b73e0-760d-49e6-8c26-da1f60068087

import Definitions.Def_WeierstrassEllipticZeta_ProjectiveChartCalculus
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FinCases

noncomputable section

open MvPolynomial Filter
open scoped Topology

open WeierstrassEllipticZeta

private lemma pderiv_degree {σ : Type} (p : MvPolynomial σ ℂ) (i : σ)
    (h : pderiv i p ≠ 0) : (pderiv i p).totalDegree + 1 ≤ p.totalDegree := by
  classical
  obtain ⟨m, hm, heq⟩ := (pderiv i p).support.exists_mem_eq_sup
    (by simpa using h) (fun m => m.sum fun _ e => e)
  have hcoeff : p.coeff (m + Finsupp.single i 1) ≠ 0 := by
    have := mem_support_iff.mp hm
    rw [coeff_pderiv] at this
    exact (mul_ne_zero_iff.mp this).1
  have hle := le_totalDegree (mem_support_iff.mpr hcoeff)
  simpa [totalDegree, heq, Finsupp.sum_add_index'] using hle

private lemma derivation_sum_apply {σ : Type} [Fintype σ]
    (F : σ → Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (p : MvPolynomial σ ℂ) : (∑ i, F i) p = ∑ i, F i p := by
  change (Derivation.coeFnAddMonoidHom (∑ i, F i)) p = _
  rw [map_sum, Finset.sum_apply]
  rfl

private lemma derivation_degree {σ : Type} [Fintype σ]
    (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (hD : ∀ i, (D (X i)).totalDegree ≤ 2) (p : MvPolynomial σ ℂ) :
    (D p).totalDegree ≤ p.totalDegree + 1 := by
  classical
  have hrepr : D = ∑ i, D (X i) • pderiv i := by
    apply MvPolynomial.derivation_ext
    intro j
    simp [derivation_sum_apply, Derivation.smul_apply, Pi.single_apply]
  have hvalue : D p = ∑ i, D (X i) * pderiv i p := by
    conv_lhs => rw [hrepr]
    simp [derivation_sum_apply]
  rw [hvalue]
  apply totalDegree_finsetSum_le
  intro i _
  by_cases hi : pderiv i p = 0
  · simp [hi]
  have hp := pderiv_degree p i hi
  have hmul := totalDegree_mul (D (X i)) (pderiv i p)
  have := hD i
  omega

private lemma hasDerivAt_eval_ode {σ : Type}
    (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (f : σ → ℂ → ℂ) (z : ℂ)
    (hf : ∀ i, HasDerivAt (f i)
      (eval (fun i => f i z) (D (X i))) z)
    (p : MvPolynomial σ ℂ) :
    HasDerivAt (fun w => eval (fun i => f i w) p)
      (eval (fun i => f i z) (D p)) z := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    simp only [derivation_C, eval_C]
    exact hasDerivAt_const z (a : ℂ)
  | add p q hp hq => simpa [Pi.add_apply] using! hp.add hq
  | mul_X p i hp =>
    simpa [D.leibniz, smul_eq_mul, add_comm, mul_comm, Pi.mul_apply] using! hp.mul (hf i)

/-- Differentiation along a quadratic polynomial ODE preserves complex polynomial
presentations, increasing their total degree by at most one at each step. -/
private theorem complex_polynomial_ode_iterated_deriv {σ : Type} [Fintype σ]
    (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (hD : ∀ i, (D (X i)).totalDegree ≤ 2)
    (U : Set ℂ) (hU : IsOpen U) (f : σ → ℂ → ℂ)
    (hf : ∀ z ∈ U, ∀ i, HasDerivAt (f i)
      (eval (fun i => f i z) (D (X i))) z)
    (p : MvPolynomial σ ℂ) (n : ℕ) :
    (D^[n] p).totalDegree ≤ p.totalDegree + n ∧
      ∀ z ∈ U, iteratedDeriv n
        (fun w => eval (fun i => f i w) p) z =
          eval (fun i => f i z) (D^[n] p) := by
  induction n with
  | zero => simp
  | succ n ih =>
    constructor
    · rw [Function.iterate_succ_apply']
      exact (derivation_degree D hD _).trans (by omega)
    · intro z hz
      rw [iteratedDeriv_succ, Function.iterate_succ_apply']
      have heq : iteratedDeriv n
          (fun w => eval (fun i => f i w) p) =ᶠ[𝓝 z]
          (fun w => eval (fun i => f i w) (D^[n] p)) :=
        Filter.Eventually.mono (hU.mem_nhds hz) fun w hw => ih.2 w hw
      rw [heq.deriv_eq]
      exact (hasDerivAt_eval_ode D f z (hf z hz) _).deriv

private theorem chart_derivation_degree (g₂ g₃ : ℂ) (c : Fin 2) (i : Fin 4) :
    (extensionChartDerivation g₂ g₃ c (X i)).totalDegree ≤ 2 := by
  have hsub (p q : MvPolynomial (Fin 4) ℂ) (hp : p.totalDegree ≤ 2)
      (hq : q.totalDegree ≤ 2) : (p - q).totalDegree ≤ 2 := by
    have hh := totalDegree_add p (-q)
    simpa [totalDegree, sub_eq_add_neg] using hh.trans (max_le hp (by simpa [totalDegree] using hq))
  have hadd (p q : MvPolynomial (Fin 4) ℂ) (hp : p.totalDegree ≤ 2)
      (hq : q.totalDegree ≤ 2) : (p + q).totalDegree ≤ 2 :=
    (totalDegree_add p q).trans (max_le hp hq)
  have hs (a : ℂ) (j : Fin 4) : (C a * X j ^ 2).totalDegree ≤ 2 := by
    apply (totalDegree_mul (C a) (X j ^ 2)).trans
    simpa using totalDegree_pow (X j : MvPolynomial (Fin 4) ℂ) 2
  have hm (a : ℂ) (j k : Fin 4) : (C a * X j * X k).totalDegree ≤ 2 := by
    have h₁ := totalDegree_mul (C a * X j) (X k)
    have h₂ := totalDegree_mul (C a) (X j)
    simp only [totalDegree_C, totalDegree_X, zero_add] at h₁ h₂
    omega
  fin_cases c <;> fin_cases i <;> simp [extensionChartDerivation]
  · exact hsub _ _ (hs 6 1) (by simp)
  · exact hadd _ _ (by simpa only [map_neg, neg_mul] using hs (-6) 2) (hs (g₂ / 2) 1)
  · exact hsub _ _ (hsub _ _ (by simp) (hm g₂ 1 2)) (hs (3 * g₃ / 2) 1)
  · exact hsub _ _ (by simpa only [map_mul, map_neg, neg_mul] using hs (-2 * g₂) 2)
      (by simpa only [map_mul] using hm (3 * g₃) 1 2)

theorem solution
    (g₂ g₃ : ℂ) (S : Fin 5 → ℂ → ℂ)
    (hS : ∀ j, AnalyticOnNhd ℂ (S j) Set.univ)
    (hflow :
      (∀ z : ℂ, S 0 z ≠ 0 →
        HasDerivAt (fun w => S 1 w / S 0 w) (S 2 z / S 0 z) z ∧
        HasDerivAt (fun w => S 2 w / S 0 w) (6 * (S 1 z / S 0 z) ^ 2 - g₂ / 2) z ∧
        HasDerivAt (fun w => S 3 w / S 0 w) (-S 1 z / S 0 z) z) ∧
      (∀ z : ℂ, S 2 z ≠ 0 →
        HasDerivAt (fun w => S 0 w / S 2 w)
          (-6 * (S 1 z / S 2 z) ^ 2 + g₂ / 2 * (S 0 z / S 2 z) ^ 2) z ∧
        HasDerivAt (fun w => S 1 w / S 2 w)
          (-(1 / 2 : ℂ) - g₂ * (S 0 z / S 2 z) * (S 1 z / S 2 z) -
            3 * g₃ / 2 * (S 0 z / S 2 z) ^ 2) z ∧
        HasDerivAt (fun w => S 4 w / S 2 w)
          (-2 * g₂ * (S 1 z / S 2 z) ^ 2 -
            3 * g₃ * (S 0 z / S 2 z) * (S 1 z / S 2 z)) z)) :
    (∀ c : Fin 2, extensionChartDerivation g₂ g₃ c (extensionChartCubic g₂ g₃ c) = 0) ∧
    ∀ (c : Fin 2) (p : MvPolynomial (Fin 4) ℂ) (n : ℕ),
      ((extensionChartDerivation g₂ g₃ c)^[n] p).totalDegree ≤ p.totalDegree + n ∧
      ∀ z : ℂ, S (extensionChartDenominator c) z ≠ 0 →
        iteratedDeriv n (fun w => MvPolynomial.eval (extensionChartCoordinates S c w) p) z =
          MvPolynomial.eval (extensionChartCoordinates S c z)
            ((extensionChartDerivation g₂ g₃ c)^[n] p) ∧
        ((n : ℕ∞) ≤ analyticOrderAt
            (fun w => MvPolynomial.eval (extensionChartCoordinates S c w) p) z ↔
          ∀ k < n, MvPolynomial.eval (extensionChartCoordinates S c z)
            ((extensionChartDerivation g₂ g₃ c)^[k] p) = 0) := by
  constructor
  · intro c
    apply MvPolynomial.funext
    intro v
    fin_cases c <;> simp [extensionChartDerivation, extensionChartCubic,
      Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul] <;> ring
  · intro c p n
    let U : Set ℂ := {z | S (extensionChartDenominator c) z ≠ 0}
    have hU : IsOpen U := (hS _).continuous.isOpen_preimage _ isOpen_ne
    have ha (z : ℂ) (hz : z ∈ U) (i : Fin 4) :
        AnalyticAt ℂ (fun w => extensionChartCoordinates S c w i) z := by
      fin_cases c <;> fin_cases i <;> simp [extensionChartCoordinates]
      all_goals first | exact analyticAt_id |
        exact (hS _ z (Set.mem_univ _)).div (hS _ z (Set.mem_univ _)) hz
    have hf (z : ℂ) (hz : z ∈ U) (i : Fin 4) :
        HasDerivAt (fun w => extensionChartCoordinates S c w i)
          (MvPolynomial.eval (extensionChartCoordinates S c z)
            (extensionChartDerivation g₂ g₃ c (X i))) z := by
      fin_cases c
      · have hh := hflow.1 z hz
        fin_cases i <;> simp [extensionChartCoordinates, extensionChartDerivation]
        · exact hasDerivAt_id z
        · exact hh.1
        · exact hh.2.1
        · simpa only [neg_div] using hh.2.2
      · have hh := hflow.2 z hz
        fin_cases i <;> simp [extensionChartCoordinates, extensionChartDerivation]
        · exact hasDerivAt_id z
        · simpa using hh.1
        · simpa using hh.2.1
        · simpa using hh.2.2
    have hj (k : ℕ) := complex_polynomial_ode_iterated_deriv
      (extensionChartDerivation g₂ g₃ c) (chart_derivation_degree g₂ g₃ c)
      U hU (fun i z => extensionChartCoordinates S c z i) hf p k
    refine ⟨(hj n).1, ?_⟩
    intro z hz
    refine ⟨(hj n).2 z hz, ?_⟩
    have hp : AnalyticAt ℂ
        (fun w => MvPolynomial.eval (extensionChartCoordinates S c w) p) z :=
      AnalyticAt.aeval_mvPolynomial (ha z hz) p
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hp]
    exact forall_congr' fun k => by simp only [(hj k).2 z hz]

