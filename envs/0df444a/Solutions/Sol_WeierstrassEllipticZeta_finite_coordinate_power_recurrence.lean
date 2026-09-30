-- Prove2me | solution 1 for WeierstrassEllipticZeta.finite_coordinate_power_recurrence
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-13T20:48:46.757498+00:00
-- url     : https://prove2.me/submissions/01e3fd0d-b71b-45e3-ad43-da315439ee8b

import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.Data.Finsupp.Order
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations

open scoped Classical

noncomputable section

theorem solution
    (K σ : Type*) [Field K] [DecidableEq σ]
    (i : σ) (T : Finset K) (N b : ℕ)
    (hfit : N * T.card ≤ b + 1) :
    ∃ r : MvPolynomial σ K,
      (∀ e ∈ r.support, e ≤ Finsupp.single i b) ∧
      ∀ (v : σ → K), v i ∈ T →
        ∀ I : Ideal (MvPolynomial σ K),
          RingHom.ker (MvPolynomial.eval v) ^ N ≤ I →
            MvPolynomial.X i ^ (b + 1) - r ∈ I := by
  classical
  let A : Polynomial K := ∏ a ∈ T, (Polynomial.X - Polynomial.C a)
  have hAm : A.Monic :=
    Polynomial.monic_prod_of_monic T _ (fun a _ => Polynomial.monic_X_sub_C a)
  have hAd : A.natDegree = T.card := by
    exact Polynomial.natDegree_finsetProd_X_sub_C_eq_card T id
  let F := A ^ N * Polynomial.X ^ (b + 1 - N * T.card)
  have hF : F.IsMonicOfDegree (b + 1) := by
    refine ⟨?_, (hAm.pow N).mul (Polynomial.monic_X_pow _)⟩
    change (A ^ N * Polynomial.X ^ (b + 1 - N * T.card)).natDegree = b + 1
    rw [Polynomial.natDegree_mul_X_pow _ (hAm.pow N).ne_zero,
      hAm.natDegree_pow N, hAd]
    omega
  obtain ⟨q, hFq, hq⟩ := hF.exists_natDegree_lt (Nat.succ_ne_zero b)
  have hsupport (w : Polynomial K) (hw : w.natDegree < b + 1) :
      ∀ e ∈ (w.toMvPolynomial i).support, e ≤ Finsupp.single i b := by
    have hexpand : w.toMvPolynomial i =
        ∑ k ∈ Finset.range (b + 1),
          MvPolynomial.monomial (Finsupp.single i k) (w.coeff k) := by
      calc
        w.toMvPolynomial i =
            (∑ k ∈ Finset.range (b + 1), Polynomial.C (w.coeff k) *
              Polynomial.X ^ k).toMvPolynomial i :=
          congrArg (Polynomial.toMvPolynomial i) (w.as_sum_range_C_mul_X_pow' hw)
        _ = _ := by
          simp only [map_sum, map_mul, map_pow, Polynomial.toMvPolynomial_C,
            Polynomial.toMvPolynomial_X, MvPolynomial.C_mul_X_pow_eq_monomial]
    intro e he
    rw [hexpand] at he
    obtain ⟨k, hk, he⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum he)
    have heq : e = Finsupp.single i k :=
      Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset he)
    rw [heq]
    apply Finsupp.single_le_single.mpr
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  refine ⟨(-q).toMvPolynomial i, hsupport (-q) ?_, ?_⟩
  · simpa only [Polynomial.natDegree_neg] using hq
  · intro v hv I hI
    have hAker : A.toMvPolynomial i ∈ RingHom.ker (MvPolynomial.eval v) := by
      apply RingHom.mem_ker.mpr
      rw [MvPolynomial.eval_toMvPolynomial]
      change Polynomial.eval (v i) (∏ a ∈ T, (Polynomial.X - Polynomial.C a)) = 0
      simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C]
      exact Finset.prod_eq_zero hv (sub_self (v i))
    have hrel : MvPolynomial.X i ^ (b + 1) - (-q).toMvPolynomial i =
        F.toMvPolynomial i := by
      rw [hFq]
      simp only [map_add, map_pow, map_neg, Polynomial.toMvPolynomial_X, sub_neg_eq_add]
    rw [hrel]
    change (A ^ N * Polynomial.X ^ (b + 1 - N * T.card)).toMvPolynomial i ∈ I
    rw [map_mul, map_pow]
    exact I.mul_mem_right _ (hI (Ideal.pow_mem_pow hAker N))
