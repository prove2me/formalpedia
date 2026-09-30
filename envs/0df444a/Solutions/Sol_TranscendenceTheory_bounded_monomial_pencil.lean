-- Prove2me | solution 1 for TranscendenceTheory.bounded_monomial_pencil
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-20T03:02:42.556976+00:00
-- url     : https://prove2.me/submissions/fbe85542-970f-4840-ae4b-7485468bfd08

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Degree
import Theorems.Thm_TranscendenceTheory_bounded_bivariate_specialization
import Theorems.Thm_TranscendenceTheory_bounded_finite_pencil_nonvanishing

open scoped Classical

private theorem eval_C_natDegree_le
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
    (c d : ι → R) :
    (∃ t : Fin (Fintype.card {i : ι // d i = 0} * a + 1),
      ∃ k : Fin (Fintype.card {i : ι // d i ≠ 0} + 1),
      (∏ i, ((F.map (Polynomial.evalRingHom (t.val : R))).eval (c i) +
        (k.val : R) * d i)) ≠ 0) ↔
    (∃ r : Fin (Fintype.card {i : ι // d i = 0} * a +
        Fintype.card {i : ι // d i ≠ 0} * (a + 1) + 1),
      (∏ i, ((F.map (Polynomial.evalRingHom (r.val : R))).eval (c i) +
        (r.val : R) ^ (a + 1) * d i)) ≠ 0) := by
  classical
  constructor
  · rintro ⟨t, k, hprod⟩
    have hnonzero (i : {i : ι // d i = 0}) :
        F.eval (Polynomial.C (c i.val)) ≠ 0 := by
      intro hz
      have hfactor := Finset.prod_ne_zero_iff.mp hprod i.val (Finset.mem_univ i.val)
      apply hfactor
      have hev : (F.map (Polynomial.evalRingHom (t.val : R))).eval (c i.val) = 0 := by
        rw [Polynomial.map_evalRingHom_eval, Polynomial.evalEval, hz, Polynomial.eval_zero]
      simp only [hev, i.property, mul_zero, zero_add]
    let p : ι → Polynomial R := fun i =>
      F.eval (Polynomial.C (c i)) + Polynomial.X ^ (a + 1) * Polynomial.C (d i)
    have hfdegree (i : ι) : (F.eval (Polynomial.C (c i))).natDegree ≤ a :=
      eval_C_natDegree_le R F a hdegree (c i)
    have hp (i : ι) : p i ≠ 0 := by
      by_cases hi : d i = 0
      · simpa only [p, hi, Polynomial.C_0, mul_zero, add_zero] using hnonzero ⟨i, hi⟩
      · intro hz
        apply hi
        have heq := congrArg (fun f : Polynomial R => f.coeff (a + 1)) hz
        have hfcoeff := Polynomial.coeff_eq_zero_of_natDegree_lt
          ((hfdegree i).trans_lt (Nat.lt_succ_self a))
        simpa [p, hfcoeff] using heq
    have hp0 (i : {i : ι // d i = 0}) : (p i.val).natDegree ≤ a := by
      simpa only [p, i.property, Polynomial.C_0, mul_zero, add_zero] using hfdegree i.val
    have hp1 (i : {i : ι // d i ≠ 0}) : (p i.val).natDegree ≤ a + 1 := by
      apply Polynomial.natDegree_add_le_of_degree_le
      · exact (hfdegree i.val).trans (Nat.le_succ a)
      · exact (Polynomial.natDegree_mul_C_le _ _).trans (by simp)
    let P0 : Polynomial R := ∏ i : {i : ι // d i = 0}, p i.val
    let P1 : Polynomial R := ∏ i : {i : ι // d i ≠ 0}, p i.val
    let Q : Polynomial R := P0 * P1
    have hQ : Q ≠ 0 := mul_ne_zero
      (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i.val))
      (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i.val))
    have hP0 : P0.natDegree ≤ Fintype.card {i : ι // d i = 0} * a := by
      calc
        P0.natDegree ≤ ∑ i : {i : ι // d i = 0}, (p i.val).natDegree :=
          Polynomial.natDegree_prod_le _ _
        _ ≤ ∑ _i : {i : ι // d i = 0}, a := Finset.sum_le_sum (fun i _ => hp0 i)
        _ = Fintype.card {i : ι // d i = 0} * a := by simp
    have hP1 : P1.natDegree ≤ Fintype.card {i : ι // d i ≠ 0} * (a + 1) := by
      calc
        P1.natDegree ≤ ∑ i : {i : ι // d i ≠ 0}, (p i.val).natDegree :=
          Polynomial.natDegree_prod_le _ _
        _ ≤ ∑ _i : {i : ι // d i ≠ 0}, (a + 1) := Finset.sum_le_sum (fun i _ => hp1 i)
        _ = Fintype.card {i : ι // d i ≠ 0} * (a + 1) := by simp
    have hQdegree : Q.natDegree ≤ Fintype.card {i : ι // d i = 0} * a +
        Fintype.card {i : ι // d i ≠ 0} * (a + 1) :=
      Polynomial.natDegree_mul_le.trans (Nat.add_le_add hP0 hP1)
    by_contra hnone
    apply hQ
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero Q
      (f := fun r : Fin (Fintype.card {i : ι // d i = 0} * a +
        Fintype.card {i : ι // d i ≠ 0} * (a + 1) + 1) => (r.val : R))
    · intro i j hij
      exact Fin.ext (Nat.cast_injective hij)
    · intro r
      by_contra hr
      apply hnone
      refine ⟨r, Finset.prod_ne_zero_iff.mpr ?_⟩
      intro i _ hi
      have heval : (p i).eval (r.val : R) = 0 := by
        simpa only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_C, Polynomial.map_evalRingHom_eval,
          Polynomial.evalEval] using hi
      apply hr
      by_cases hdi : d i = 0
      · have hP0eval : P0.eval (r.val : R) = 0 := by
          simp only [P0, Polynomial.eval_prod]
          exact Finset.prod_eq_zero (Finset.mem_univ (⟨i, hdi⟩ : {i : ι // d i = 0})) heval
        simp only [Q, Polynomial.eval_mul, hP0eval, zero_mul]
      · have hP1eval : P1.eval (r.val : R) = 0 := by
          simp only [P1, Polynomial.eval_prod]
          exact Finset.prod_eq_zero (Finset.mem_univ (⟨i, hdi⟩ : {i : ι // d i ≠ 0})) heval
        simp only [Q, Polynomial.eval_mul, hP1eval, mul_zero]
    · simpa only [Fintype.card_fin] using Nat.lt_succ_of_le hQdegree
  · rintro ⟨r, hprod⟩
    have hnonzero (i : {i : ι // d i = 0}) :
        F.eval (Polynomial.C (c i.val)) ≠ 0 := by
      intro hz
      have hfactor := Finset.prod_ne_zero_iff.mp hprod i.val (Finset.mem_univ i.val)
      apply hfactor
      have hev : (F.map (Polynomial.evalRingHom (r.val : R))).eval (c i.val) = 0 := by
        rw [Polynomial.map_evalRingHom_eval, Polynomial.evalEval, hz, Polynomial.eval_zero]
      simp only [hev, i.property, mul_zero, zero_add]
    obtain ⟨t, ht⟩ := (TranscendenceTheory.bounded_bivariate_specialization
      R {i : ι // d i = 0} F a hdegree (fun i => c i.val) (fun _ => True)).mp
        (fun i _ => hnonzero i)
    have hpair : ∀ i : {i : ι // d i ≠ 0}, d i.val = 0 →
        (F.map (Polynomial.evalRingHom (t.val : R))).eval (c i.val) ≠ 0 := by
      intro i hi
      exact (i.property hi).elim
    obtain ⟨k, hk⟩ := (TranscendenceTheory.bounded_finite_pencil_nonvanishing
      R {i : ι // d i ≠ 0}
      (fun i => (F.map (Polynomial.evalRingHom (t.val : R))).eval (c i.val))
      (fun i => d i.val)).mp hpair
    refine ⟨t, k, Finset.prod_ne_zero_iff.mpr ?_⟩
    intro i _
    by_cases hi : d i = 0
    · simpa only [hi, mul_zero, add_zero] using ht ⟨i, hi⟩ trivial
    · exact Finset.prod_ne_zero_iff.mp hk ⟨i, hi⟩
        (Finset.mem_univ (⟨i, hi⟩ : {i : ι // d i ≠ 0}))
