-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_family_bounded_generic_nonvanishing
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T21:23:50.095689+00:00
-- url     : https://prove2.me/submissions/1e98c011-e9cd-44e8-ba35-7391335e6a70

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Complex.Basic

noncomputable section
open scoped Classical



theorem solution
    (V : Finset (Fin 4 → ℂ)) (K : ℕ) (f : Fin K → MvPolynomial (Fin 4) ℂ)
    (h : ∀ v : V, ∃ j : Fin K, MvPolynomial.eval v.val (f j) ≠ 0) :
    ∃ a : ℕ, a ≤ V.card * (K - 1) ∧
      let q := ∑ j : Fin K, MvPolynomial.C ((a : ℂ) ^ j.val) * f j
      (∀ v : V, MvPolynomial.eval v.val q ≠ 0) ∧
      ∀ D : ℕ, (∀ j : Fin K, (f j).totalDegree ≤ D) → q.totalDegree ≤ D := by
  classical
  let F : V → Polynomial ℂ := fun v =>
    ∑ j : Fin K, Polynomial.monomial j.val (MvPolynomial.eval v.val (f j))
  have hcoeff (v : V) (j : Fin K) :
      (F v).coeff j.val = MvPolynomial.eval v.val (f j) := by
    simp [F, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial, Fin.val_inj]
  have hF (v : V) : F v ≠ 0 := by
    obtain ⟨j, hj⟩ := h v
    intro hz
    apply hj
    rw [← hcoeff v j, hz, Polynomial.coeff_zero]
  have hprod : (∏ v : V, F v) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun v _ => hF v)
  have hdegree (v : V) : (F v).natDegree ≤ K - 1 := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j _
    exact (Polynomial.natDegree_monomial_le _).trans (Nat.le_sub_one_of_lt j.isLt)
  have hproddegree : (∏ v : V, F v).natDegree ≤ V.card * (K - 1) := by
    apply (Polynomial.natDegree_prod_le _ _).trans
    calc
      ∑ v : V, (F v).natDegree ≤ ∑ _v : V, (K - 1) :=
        Finset.sum_le_sum (fun v _ => hdegree v)
      _ = V.card * (K - 1) := by simp
  obtain ⟨a, ha⟩ : ∃ a : Fin (V.card * (K - 1) + 1),
      (∏ v : V, F v).eval (a.val : ℂ) ≠ 0 := by
    by_contra! hz
    apply hprod
    refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ ?_ hz ?_
    · intro a b hab
      exact Fin.ext (Nat.cast_inj.mp hab)
    · simpa only [Fintype.card_fin] using Nat.lt_succ_of_le hproddegree
  refine ⟨a.val, Nat.le_of_lt_succ a.isLt, ?_, ?_⟩
  · intro v
    have hall : ∏ w : V, (F w).eval (a.val : ℂ) ≠ 0 := by
      simpa only [Polynomial.eval_prod] using ha
    have hv := Finset.prod_ne_zero_iff.mp hall v (Finset.mem_univ v)
    simpa [F, Polynomial.eval_finsetSum, Polynomial.eval_monomial, mul_comm] using hv
  · intro D hD
    apply MvPolynomial.totalDegree_finsetSum_le
    intro j _
    rw [MvPolynomial.C_mul']
    exact (MvPolynomial.totalDegree_smul_le _ _).trans (hD j)

