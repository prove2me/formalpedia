-- Prove2me | solution 1 for TranscendenceTheory.partitioned_bivariate_pencil_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-20T02:04:36.082+00:00
-- url     : https://prove2.me/submissions/f72e467a-2879-4fab-96eb-cec99e0fca1d

import Theorems.Thm_TranscendenceTheory_bounded_bivariate_specialization
import Theorems.Thm_TranscendenceTheory_bounded_finite_pencil_nonvanishing

open scoped Classical

theorem solution
    (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
    (ι : Type*) [Fintype ι] (F : Polynomial (Polynomial R))
    (a : ℕ) (hdegree : ∀ j, (F.coeff j).natDegree ≤ a)
    (c d : ι → R) :
    (∃ t : Fin (Fintype.card ι * a + 1), ∃ k : Fin (Fintype.card ι + 1),
      (∏ i, ((F.map (Polynomial.evalRingHom (t.val : R))).eval (c i) +
        (k.val : R) * d i)) ≠ 0) ↔
    (∃ t : Fin (Fintype.card {i : ι // d i = 0} * a + 1),
      ∃ k : Fin (Fintype.card {i : ι // d i ≠ 0} + 1),
      (∏ i, ((F.map (Polynomial.evalRingHom (t.val : R))).eval (c i) +
        (k.val : R) * d i)) ≠ 0) := by
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
    obtain ⟨t', ht'⟩ := (TranscendenceTheory.bounded_bivariate_specialization
      R {i : ι // d i = 0} F a hdegree (fun i => c i.val) (fun _ => True)).mp
        (fun i _ => hnonzero i)
    have hpair : ∀ i : {i : ι // d i ≠ 0}, d i.val = 0 →
        (F.map (Polynomial.evalRingHom (t'.val : R))).eval (c i.val) ≠ 0 := by
      intro i hi
      exact (i.property hi).elim
    obtain ⟨k', hk'⟩ := (TranscendenceTheory.bounded_finite_pencil_nonvanishing
      R {i : ι // d i ≠ 0}
      (fun i => (F.map (Polynomial.evalRingHom (t'.val : R))).eval (c i.val))
      (fun i => d i.val)).mp hpair
    refine ⟨t', k', Finset.prod_ne_zero_iff.mpr ?_⟩
    intro i _
    by_cases hi : d i = 0
    · simpa only [hi, mul_zero, add_zero] using ht' ⟨i, hi⟩ trivial
    · exact Finset.prod_ne_zero_iff.mp hk' ⟨i, hi⟩
        (Finset.mem_univ (⟨i, hi⟩ : {i : ι // d i ≠ 0}))
  · rintro ⟨t, k, hprod⟩
    have hzero : Fintype.card {i : ι // d i = 0} ≤ Fintype.card ι :=
      Fintype.card_le_of_injective (fun i : {i : ι // d i = 0} => i.val)
        Subtype.val_injective
    have hnonzero : Fintype.card {i : ι // d i ≠ 0} ≤ Fintype.card ι :=
      Fintype.card_le_of_injective (fun i : {i : ι // d i ≠ 0} => i.val)
        Subtype.val_injective
    let t' : Fin (Fintype.card ι * a + 1) := ⟨t.val,
      t.isLt.trans_le (Nat.add_le_add_right (Nat.mul_le_mul_right a hzero) 1)⟩
    let k' : Fin (Fintype.card ι + 1) := ⟨k.val,
      k.isLt.trans_le (Nat.add_le_add_right hnonzero 1)⟩
    exact ⟨t', k', hprod⟩
