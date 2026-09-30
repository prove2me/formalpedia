-- Prove2me | solution 1 for TranscendenceTheory.bounded_finite_pencil_nonvanishing
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-20T01:06:31.990391+00:00
-- url     : https://prove2.me/submissions/8d563692-4b2e-4e73-ab14-4bf80f9d2434

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Degree

theorem solution
    (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
    (ι : Type*) [Fintype ι] (u v : ι → R) :
    (∀ i, v i = 0 → u i ≠ 0) ↔
      ∃ n : Fin (Fintype.card ι + 1), (∏ i, (u i + (n.val : R) * v i)) ≠ 0 := by
  classical
  constructor
  · intro hpair
    let p : ι → Polynomial R := fun i =>
      Polynomial.C (u i) + Polynomial.X * Polynomial.C (v i)
    have hp (i : ι) : p i ≠ 0 := by
      intro hz
      have hv : v i = 0 := by
        have heq := congrArg (fun f : Polynomial R => f.coeff 1) hz
        simpa [p] using heq
      apply hpair i hv
      have heq := congrArg (Polynomial.eval 0) hz
      simpa only [p, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
        Polynomial.eval_X, Polynomial.eval_zero, zero_mul, add_zero] using heq
    have hdegree (i : ι) : (p i).natDegree ≤ 1 := by
      apply Polynomial.natDegree_add_le_of_degree_le
      · simp
      · exact (Polynomial.natDegree_mul_C_le _ _).trans (by simp)
    let q : Polynomial R := ∏ i, p i
    have hq : q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
    have hqdegree : q.natDegree ≤ Fintype.card ι := by
      calc
        q.natDegree ≤ ∑ i : ι, (p i).natDegree := Polynomial.natDegree_prod_le _ _
        _ ≤ ∑ _i : ι, 1 := Finset.sum_le_sum (fun i _ => hdegree i)
        _ = Fintype.card ι := by simp
    by_contra hnone
    apply hq
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero q
      (f := fun n : Fin (Fintype.card ι + 1) => (n.val : R))
    · intro i j hij
      exact Fin.ext (Nat.cast_injective hij)
    · intro n
      by_contra hn
      apply hnone
      refine ⟨n, ?_⟩
      simpa only [q, p, Polynomial.eval_prod, Polynomial.eval_add, Polynomial.eval_C,
        Polynomial.eval_mul, Polynomial.eval_X] using hn
    · simpa only [Fintype.card_fin] using Nat.lt_succ_of_le hqdegree
  · rintro ⟨n, hn⟩ i hvi hui
    apply hn
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [hui, hvi, mul_zero, add_zero]
