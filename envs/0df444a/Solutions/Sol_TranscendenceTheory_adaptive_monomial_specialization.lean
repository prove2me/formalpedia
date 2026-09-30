-- Prove2me | solution 1 for TranscendenceTheory.adaptive_monomial_specialization
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-20T03:25:37.541854+00:00
-- url     : https://prove2.me/submissions/4563a1a2-daac-42e4-a579-ccc7f11aef8b

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Degree

open scoped Classical

private theorem weighted_monomial_specialization
    (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
    (ι : Type*) [Fintype ι] (f : ι → Polynomial R) (d : ι → R)
    (b : ℕ) (hdegree : ∀ i, d i ≠ 0 → (f i).natDegree ≤ b)
    (hnonzero : ∀ i, d i = 0 → f i ≠ 0) :
    ∃ r : Fin ((∑ i : {i : ι // d i = 0}, (f i.val).natDegree) +
        Fintype.card {i : ι // d i ≠ 0} * (b + 1) + 1),
      (∏ i, ((f i).eval (r.val : R) + (r.val : R) ^ (b + 1) * d i)) ≠ 0 := by
  classical
  let p : ι → Polynomial R := fun i =>
    f i + Polynomial.X ^ (b + 1) * Polynomial.C (d i)
  have hp (i : ι) : p i ≠ 0 := by
    by_cases hi : d i = 0
    · simpa only [p, hi, Polynomial.C_0, mul_zero, add_zero] using hnonzero i hi
    · intro hz
      apply hi
      have heq := congrArg (fun g : Polynomial R => g.coeff (b + 1)) hz
      have hfcoeff := Polynomial.coeff_eq_zero_of_natDegree_lt
        ((hdegree i hi).trans_lt (Nat.lt_succ_self b))
      simpa [p, hfcoeff] using heq
  have hp0 (i : {i : ι // d i = 0}) : (p i.val).natDegree ≤ (f i.val).natDegree := by
    simp only [p, i.property, Polynomial.C_0, mul_zero, add_zero, le_refl]
  have hp1 (i : {i : ι // d i ≠ 0}) : (p i.val).natDegree ≤ b + 1 := by
    apply Polynomial.natDegree_add_le_of_degree_le
    · exact (hdegree i.val i.property).trans (Nat.le_succ b)
    · exact (Polynomial.natDegree_mul_C_le _ _).trans (by simp)
  let P0 : Polynomial R := ∏ i : {i : ι // d i = 0}, p i.val
  let P1 : Polynomial R := ∏ i : {i : ι // d i ≠ 0}, p i.val
  let Q : Polynomial R := P0 * P1
  have hQ : Q ≠ 0 := mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i.val))
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i.val))
  have hP0 : P0.natDegree ≤ ∑ i : {i : ι // d i = 0}, (f i.val).natDegree :=
    (Polynomial.natDegree_prod_le _ _).trans (Finset.sum_le_sum (fun i _ => hp0 i))
  have hP1 : P1.natDegree ≤ Fintype.card {i : ι // d i ≠ 0} * (b + 1) := by
    calc
      P1.natDegree ≤ ∑ i : {i : ι // d i ≠ 0}, (p i.val).natDegree :=
        Polynomial.natDegree_prod_le _ _
      _ ≤ ∑ _i : {i : ι // d i ≠ 0}, (b + 1) := Finset.sum_le_sum (fun i _ => hp1 i)
      _ = Fintype.card {i : ι // d i ≠ 0} * (b + 1) := by simp
  have hQdegree : Q.natDegree ≤ (∑ i : {i : ι // d i = 0}, (f i.val).natDegree) +
      Fintype.card {i : ι // d i ≠ 0} * (b + 1) :=
    Polynomial.natDegree_mul_le.trans (Nat.add_le_add hP0 hP1)
  by_contra hnone
  apply hQ
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero Q
    (f := fun r : Fin ((∑ i : {i : ι // d i = 0}, (f i.val).natDegree) +
      Fintype.card {i : ι // d i ≠ 0} * (b + 1) + 1) => (r.val : R))
  · intro i j hij
    exact Fin.ext (Nat.cast_injective hij)
  · intro r
    by_contra hr
    apply hnone
    refine ⟨r, Finset.prod_ne_zero_iff.mpr ?_⟩
    intro i _ hi
    have heval : (p i).eval (r.val : R) = 0 := by
      simpa only [p, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C] using hi
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

theorem solution
    (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
    (ι : Type*) [Fintype ι] (f : ι → Polynomial R) (d : ι → R)
    (a : ℕ) (hdegree : ∀ i, (f i).natDegree ≤ a) :
    let b : ℕ := Finset.univ.sup (fun i : {i : ι // d i ≠ 0} => (f i.val).natDegree)
    b ≤ a ∧
    ((∑ i : {i : ι // d i = 0}, (f i.val).natDegree) +
      Fintype.card {i : ι // d i ≠ 0} * (b + 1) ≤
      Fintype.card {i : ι // d i = 0} * a + Fintype.card {i : ι // d i ≠ 0} * (a + 1)) ∧
    ((∃ r : Fin (Fintype.card {i : ι // d i = 0} * a +
        Fintype.card {i : ι // d i ≠ 0} * (a + 1) + 1),
      (∏ i, ((f i).eval (r.val : R) + (r.val : R) ^ (a + 1) * d i)) ≠ 0) ↔
    (∃ r : Fin ((∑ i : {i : ι // d i = 0}, (f i.val).natDegree) +
        Fintype.card {i : ι // d i ≠ 0} * (b + 1) + 1),
      (∏ i, ((f i).eval (r.val : R) + (r.val : R) ^ (b + 1) * d i)) ≠ 0)) := by
  classical
  dsimp only
  let b : ℕ := Finset.univ.sup (fun i : {i : ι // d i ≠ 0} => (f i.val).natDegree)
  have hb : b ≤ a := Finset.sup_le (fun i _ => hdegree i.val)
  have hsum : (∑ i : {i : ι // d i = 0}, (f i.val).natDegree) ≤
      Fintype.card {i : ι // d i = 0} * a := by
    calc
      _ ≤ ∑ _i : {i : ι // d i = 0}, a := Finset.sum_le_sum (fun i _ => hdegree i.val)
      _ = _ := by simp
  refine ⟨hb, Nat.add_le_add hsum (Nat.mul_le_mul_left _ (Nat.add_le_add_right hb 1)), ?_⟩
  constructor
  · rintro ⟨r, hprod⟩
    have hnonzero : ∀ i, d i = 0 → f i ≠ 0 := by
      intro i hi hz
      have hfactor := Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i)
      apply hfactor
      simp only [hz, Polynomial.eval_zero, hi, mul_zero, zero_add]
    apply weighted_monomial_specialization R ι f d b _ hnonzero
    intro i hi
    exact Finset.le_sup (f := fun i : {i : ι // d i ≠ 0} => (f i.val).natDegree)
      (Finset.mem_univ (⟨i, hi⟩ : {i : ι // d i ≠ 0}))
  · rintro ⟨r, hprod⟩
    have hnonzero : ∀ i, d i = 0 → f i ≠ 0 := by
      intro i hi hz
      have hfactor := Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i)
      apply hfactor
      simp only [hz, Polynomial.eval_zero, hi, mul_zero, zero_add]
    obtain ⟨r', hr'⟩ := weighted_monomial_specialization R ι f d a
      (fun i _ => hdegree i) hnonzero
    let r'' : Fin (Fintype.card {i : ι // d i = 0} * a +
        Fintype.card {i : ι // d i ≠ 0} * (a + 1) + 1) := ⟨r'.val,
      r'.isLt.trans_le (Nat.add_le_add_right (Nat.add_le_add_right hsum _) 1)⟩
    exact ⟨r'', hr'⟩
