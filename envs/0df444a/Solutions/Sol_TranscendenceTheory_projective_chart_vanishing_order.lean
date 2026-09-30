-- Prove2me | solution 1 for TranscendenceTheory.projective_chart_vanishing_order
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T15:08:02.579098+00:00
-- url     : https://prove2.me/submissions/83cac968-514b-4bfd-ba5b-e3813771cd5f

import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

noncomputable section


private lemma p2m_last_block_scaling (R : Type*) [CommSemiring R]
    (Q : MvPolynomial (Fin 7) R) (n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (x : Fin 7 → R) (r : R) :
    MvPolynomial.eval ![x 0, x 1, r * x 2, r * x 3, r * x 4, r * x 5, r * x 6] Q =
      r ^ n * MvPolynomial.eval x Q := by
  classical
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← hQ d hd]
  simp [Fin.prod_univ_seven, mul_pow, pow_add]
  ring

theorem solution
    (A : Fin 2 → ℂ → ℂ) (S : Fin 5 → ℂ → ℂ)
    (Q : MvPolynomial (Fin 7) ℂ) (n : ℕ)
    (hQ : ∀ d ∈ Q.support, d 2 + d 3 + d 4 + d 5 + d 6 = n)
    (z : ℂ) (j : Fin 5) (hj : S j z ≠ 0)
    (hA : ∀ i, AnalyticAt ℂ (A i) z) (hS : ∀ i, AnalyticAt ℂ (S i) z) :
    let F : ℂ → ℂ := fun w => MvPolynomial.eval
      ![A 0 w, A 1 w, S 0 w, S 1 w, S 2 w, S 3 w, S 4 w] Q
    let Fⱼ : ℂ → ℂ := fun w => MvPolynomial.eval
      ![A 0 w, A 1 w, S 0 w / S j w, S 1 w / S j w,
        S 2 w / S j w, S 3 w / S j w, S 4 w / S j w] Q
    AnalyticAt ℂ F z ∧ AnalyticAt ℂ Fⱼ z ∧
      analyticOrderAt F z = analyticOrderAt Fⱼ z ∧
      ∀ T : ℕ, analyticOrderAt Fⱼ z ≤ T ↔
        ∃ k : ℕ, k ≤ T ∧ iteratedDeriv k F z ≠ 0 := by
  classical
  let F : ℂ → ℂ := fun w => MvPolynomial.eval
    ![A 0 w, A 1 w, S 0 w, S 1 w, S 2 w, S 3 w, S 4 w] Q
  let Fⱼ : ℂ → ℂ := fun w => MvPolynomial.eval
    ![A 0 w, A 1 w, S 0 w / S j w, S 1 w / S j w,
      S 2 w / S j w, S 3 w / S j w, S 4 w / S j w] Q
  change AnalyticAt ℂ F z ∧ AnalyticAt ℂ Fⱼ z ∧
    analyticOrderAt F z = analyticOrderAt Fⱼ z ∧
    ∀ T : ℕ, analyticOrderAt Fⱼ z ≤ T ↔
      ∃ k : ℕ, k ≤ T ∧ iteratedDeriv k F z ≠ 0
  have hF : AnalyticAt ℂ F z := by
    apply AnalyticAt.aeval_mvPolynomial
    intro i
    fin_cases i
    · exact hA 0
    · exact hA 1
    · exact hS 0
    · exact hS 1
    · exact hS 2
    · exact hS 3
    · exact hS 4
  have hu : AnalyticAt ℂ (fun w => (S j w)⁻¹ ^ n) z := ((hS j).inv hj).pow n
  have hscale : Fⱼ = (fun w => (S j w)⁻¹ ^ n) * F := by
    funext w
    simpa [F, Fⱼ, div_eq_mul_inv, mul_comm] using
      p2m_last_block_scaling ℂ Q n hQ
        ![A 0 w, A 1 w, S 0 w, S 1 w, S 2 w, S 3 w, S 4 w] (S j w)⁻¹
  have hFⱼ : AnalyticAt ℂ Fⱼ z := by
    rw [hscale]
    exact hu.mul hF
  have horder : analyticOrderAt F z = analyticOrderAt Fⱼ z := by
    rw [hscale, analyticOrderAt_mul hu hF,
      hu.analyticOrderAt_eq_zero.mpr (pow_ne_zero n (inv_ne_zero hj)), zero_add]
  refine ⟨hF, hFⱼ, horder, ?_⟩
  intro T
  rw [← horder]
  have hjet := not_congr
    (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (n := T + 1) hF)
  push Not at hjet
  simpa only [Nat.cast_add, Nat.cast_one, ENat.lt_natCast_add_one_iff,
    Nat.lt_succ_iff] using hjet

