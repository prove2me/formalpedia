-- Prove2me | solution 1 for TranscendenceTheory.bounded_bivariate_specialization
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-20T00:52:47.828345+00:00
-- url     : https://prove2.me/submissions/1af6b141-e358-4c2b-a6ab-ccd4399ccd2a

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Algebra.Polynomial.Eval.Degree

private theorem finite_polynomial_family_nat_specialization
    (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
    (ι : Type*) [Fintype ι] (p : ι → Polynomial R) (a : ℕ)
    (hp : ∀ i, p i ≠ 0) (hdegree : ∀ i, (p i).natDegree ≤ a) :
    ∃ n : Fin (Fintype.card ι * a + 1), ∀ i, (p i).eval (n.val : R) ≠ 0 := by
  classical
  let q : Polynomial R := ∏ i, p i
  have hq : q ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hqdegree : q.natDegree ≤ Fintype.card ι * a := by
    calc
      q.natDegree ≤ ∑ i : ι, (p i).natDegree := Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ _i : ι, a := Finset.sum_le_sum (fun i _ => hdegree i)
      _ = Fintype.card ι * a := by simp
  by_contra hnone
  apply hq
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero q
    (f := fun n : Fin (Fintype.card ι * a + 1) => (n.val : R))
  · intro i j hij
    exact Fin.ext (Nat.cast_injective hij)
  · intro n
    by_contra hn
    apply hnone
    refine ⟨n, ?_⟩
    intro i hi
    apply hn
    simp only [q, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) hi
  · simpa only [Fintype.card_fin] using Nat.lt_succ_of_le hqdegree

private theorem natDegree_eval_C_le_of_coeff_bound
    (R : Type*) [CommRing R] (F : Polynomial (Polynomial R))
    (a : ℕ) (hdegree : ∀ j, (F.coeff j).natDegree ≤ a) (c : R) :
    (F.eval (Polynomial.C c)).natDegree ≤ a := by
  rw [Polynomial.eval_eq_sum_range]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  rw [← Polynomial.C_pow]
  exact (Polynomial.natDegree_mul_C_le _ _).trans (hdegree j)

theorem solution
    (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
    (ι : Type*) [Fintype ι] (F : Polynomial (Polynomial R))
    (a : ℕ) (hdegree : ∀ j, (F.coeff j).natDegree ≤ a)
    (c : ι → R) (active : ι → Prop) :
    (∀ i, active i → F.eval (Polynomial.C (c i)) ≠ 0) ↔
      ∃ n : Fin (Fintype.card ι * a + 1), ∀ i, active i →
        (F.map (Polynomial.evalRingHom (n.val : R))).eval (c i) ≠ 0 := by
  classical
  constructor
  · intro hnonzero
    let p : ι → Polynomial R := fun i =>
      if active i then F.eval (Polynomial.C (c i)) else 1
    have hp (i : ι) : p i ≠ 0 := by
      by_cases hi : active i
      · simpa only [p, if_pos hi] using hnonzero i hi
      · simp only [p, if_neg hi, ne_eq, one_ne_zero, not_false_eq_true]
    have hdeg (i : ι) : (p i).natDegree ≤ a := by
      by_cases hi : active i
      · simpa only [p, if_pos hi] using
          natDegree_eval_C_le_of_coeff_bound R F a hdegree (c i)
      · simp only [p, if_neg hi, Polynomial.natDegree_one, Nat.zero_le]
    obtain ⟨n, hn⟩ := finite_polynomial_family_nat_specialization R ι p a hp hdeg
    refine ⟨n, ?_⟩
    intro i hi
    simpa only [p, if_pos hi, Polynomial.map_evalRingHom_eval, Polynomial.evalEval]
      using hn i
  · rintro ⟨n, hn⟩ i hi hzero
    apply hn i hi
    rw [Polynomial.map_evalRingHom_eval, Polynomial.evalEval, hzero, Polynomial.eval_zero]
