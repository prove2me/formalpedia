-- Prove2me | solution 1 for TranscendenceTheory.surjective_partitioned_pencil_bounds
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-20T02:26:45.09328+00:00
-- url     : https://prove2.me/submissions/26cc63ab-662d-44e0-bc0d-40c9497aa086

import Theorems.Thm_TranscendenceTheory_bounded_bivariate_specialization
import Theorems.Thm_TranscendenceTheory_bounded_finite_pencil_nonvanishing

open scoped Classical

theorem solution
    (R : Type*) [CommRing R] [IsDomain R] [CharZero R]
    (ι κ : Type*) [Fintype ι] [Fintype κ]
    (π : ι → κ) (hπ : Function.Surjective π)
    (F : Polynomial (Polynomial R)) (a : ℕ)
    (hdegree : ∀ j, (F.coeff j).natDegree ≤ a) (c d : κ → R) :
    (∃ t : Fin (Fintype.card {i : ι // d (π i) = 0} * a + 1),
      ∃ k : Fin (Fintype.card {i : ι // d (π i) ≠ 0} + 1),
      (∏ i, ((F.map (Polynomial.evalRingHom (t.val : R))).eval (c (π i)) +
        (k.val : R) * d (π i))) ≠ 0) ↔
    (∃ t : Fin (Fintype.card {j : κ // d j = 0} * a + 1),
      ∃ k : Fin (Fintype.card {j : κ // d j ≠ 0} + 1),
      (∏ j, ((F.map (Polynomial.evalRingHom (t.val : R))).eval (c j) +
        (k.val : R) * d j)) ≠ 0) := by
  classical
  constructor
  · rintro ⟨t, k, hprod⟩
    have hnonzero (j : {j : κ // d j = 0}) :
        F.eval (Polynomial.C (c j.val)) ≠ 0 := by
      intro hz
      obtain ⟨i, hi⟩ := hπ j.val
      have hfactor := Finset.prod_ne_zero_iff.mp hprod i (Finset.mem_univ i)
      apply hfactor
      have hd : d (π i) = 0 := by rw [hi]; exact j.property
      have hev : (F.map (Polynomial.evalRingHom (t.val : R))).eval (c (π i)) = 0 := by
        rw [hi, Polynomial.map_evalRingHom_eval, Polynomial.evalEval, hz, Polynomial.eval_zero]
      simp only [hev, hd, mul_zero, zero_add]
    obtain ⟨t', ht'⟩ := (TranscendenceTheory.bounded_bivariate_specialization
      R {j : κ // d j = 0} F a hdegree (fun j => c j.val) (fun _ => True)).mp
        (fun j _ => hnonzero j)
    have hpair : ∀ j : {j : κ // d j ≠ 0}, d j.val = 0 →
        (F.map (Polynomial.evalRingHom (t'.val : R))).eval (c j.val) ≠ 0 := by
      intro j hj
      exact (j.property hj).elim
    obtain ⟨k', hk'⟩ := (TranscendenceTheory.bounded_finite_pencil_nonvanishing
      R {j : κ // d j ≠ 0}
      (fun j => (F.map (Polynomial.evalRingHom (t'.val : R))).eval (c j.val))
      (fun j => d j.val)).mp hpair
    refine ⟨t', k', Finset.prod_ne_zero_iff.mpr ?_⟩
    intro j _
    by_cases hj : d j = 0
    · simpa only [hj, mul_zero, add_zero] using ht' ⟨j, hj⟩ trivial
    · exact Finset.prod_ne_zero_iff.mp hk' ⟨j, hj⟩
        (Finset.mem_univ (⟨j, hj⟩ : {j : κ // d j ≠ 0}))
  · rintro ⟨t, k, hprod⟩
    let π₀ : {i : ι // d (π i) = 0} → {j : κ // d j = 0} :=
      fun i => ⟨π i.val, i.property⟩
    have hπ₀ : Function.Surjective π₀ := by
      intro j
      obtain ⟨i, hi⟩ := hπ j.val
      refine ⟨⟨i, ?_⟩, Subtype.ext hi⟩
      rw [hi]
      exact j.property
    let π₁ : {i : ι // d (π i) ≠ 0} → {j : κ // d j ≠ 0} :=
      fun i => ⟨π i.val, i.property⟩
    have hπ₁ : Function.Surjective π₁ := by
      intro j
      obtain ⟨i, hi⟩ := hπ j.val
      refine ⟨⟨i, ?_⟩, Subtype.ext hi⟩
      rw [hi]
      exact j.property
    have hzero := Fintype.card_le_of_surjective π₀ hπ₀
    have hnonzero := Fintype.card_le_of_surjective π₁ hπ₁
    let t' : Fin (Fintype.card {i : ι // d (π i) = 0} * a + 1) := ⟨t.val,
      t.isLt.trans_le (Nat.add_le_add_right (Nat.mul_le_mul_right a hzero) 1)⟩
    let k' : Fin (Fintype.card {i : ι // d (π i) ≠ 0} + 1) := ⟨k.val,
      k.isLt.trans_le (Nat.add_le_add_right hnonzero 1)⟩
    refine ⟨t', k', Finset.prod_ne_zero_iff.mpr ?_⟩
    intro i _
    exact Finset.prod_ne_zero_iff.mp hprod (π i) (Finset.mem_univ (π i))
