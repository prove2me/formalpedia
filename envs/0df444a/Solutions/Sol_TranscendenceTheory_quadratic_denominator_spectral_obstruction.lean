-- Prove2me | solution 1 for TranscendenceTheory.quadratic_denominator_spectral_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-14T23:09:05.273326+00:00
-- url     : https://prove2.me/submissions/c4b5d308-1133-46f0-93a0-aa8c58d48361

import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.ComputeDegree

open Polynomial

private lemma product_degree_bound {R ι : Type*} [CommSemiring R]
    (s : Finset ι) (q : ι → Polynomial R) (d : ℕ)
    (hq : ∀ r ∈ s, (q r).natDegree ≤ d) :
    (∏ r ∈ s, q r).natDegree ≤ d * s.card := by
  apply (Polynomial.natDegree_prod_le s q).trans
  calc
    ∑ r ∈ s, (q r).natDegree ≤ ∑ _r ∈ s, d := Finset.sum_le_sum hq
    _ = d * s.card := by simp [Nat.mul_comm]

private lemma reflect_power_bound {R : Type*} [CommSemiring R]
    (q : Polynomial R) (d N : ℕ) (hq : q.natDegree ≤ d) :
    reflect (d * N) (q ^ N) = (reflect d q) ^ N := by
  induction N with
  | zero => simp [reflect_one]
  | succ N ih =>
    rw [Nat.mul_succ, pow_succ, reflect_mul _ _
      (by simpa [Nat.mul_comm] using natDegree_pow_le_of_le N hq) hq, ih, pow_succ]

private lemma reflect_product_bound {R ι : Type*} [CommSemiring R]
    (s : Finset ι) (q : ι → Polynomial R) (d : ℕ)
    (hq : ∀ r ∈ s, (q r).natDegree ≤ d) :
    reflect (d * s.card) (∏ r ∈ s, q r) = ∏ r ∈ s, reflect d (q r) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [reflect_one]
  | @insert r s hr ih =>
    have hqr := hq r (Finset.mem_insert_self r s)
    have hqs : ∀ t ∈ s, (q t).natDegree ≤ d := fun t ht =>
      hq t (Finset.mem_insert_of_mem ht)
    simp only [Finset.prod_insert hr, Finset.card_insert_of_notMem hr, Nat.mul_succ]
    rw [Nat.add_comm (d * s.card) d,
      reflect_mul _ _ hqr (product_degree_bound s q d hqs), ih hqs]

theorem solution
    (R ι : Type*) [CommRing R] [IsDomain R] [Fintype ι]
    (a c : ι → R) (N : ℕ) (A : Polynomial R) (z : R)
    (hA : A.degree < ((2 * N * Fintype.card ι : ℕ) : WithBot ℕ))
    (h : (1 - C z * X) * A =
      ∏ r : ι, (1 - C (a r) * X + C (c r) * X ^ 2) ^ N) :
    ∃ r : ι, z ^ 2 - a r * z + c r = 0 := by
  classical
  let q : ι → Polynomial R := fun r => 1 - C (a r) * X + C (c r) * X ^ 2
  let d := 2 * N * Fintype.card ι
  change (1 - C z * X) * A = ∏ r : ι, q r ^ N at h
  have hq (r : ι) : (q r).natDegree ≤ 2 := by
    dsimp only [q]
    compute_degree
  have hqN (r : ι) : (q r ^ N).natDegree ≤ 2 * N := by
    simpa [Nat.mul_comm] using natDegree_pow_le_of_le N (hq r)
  have hconstant : (∏ r : ι, q r ^ N).coeff 0 = 1 := by
    change Polynomial.constantCoeff (∏ r : ι, q r ^ N) = 1
    simp only [map_prod, map_pow]
    change (∏ r : ι, (q r).coeff 0 ^ N) = 1
    simp [q]
  have ha : A ≠ 0 := by
    intro ha
    have hzero : (∏ r : ι, q r ^ N).coeff 0 = 0 := by rw [← h, ha, mul_zero, coeff_zero]
    rw [hconstant] at hzero
    exact one_ne_zero hzero
  have hAn : A.natDegree < d := (natDegree_lt_iff_degree_lt ha).mpr hA
  have hd : d = 1 + (d - 1) := by omega
  have hAn' : A.natDegree ≤ d - 1 := by omega
  have hf : (1 - C z * X : Polynomial R).natDegree ≤ 1 := by compute_degree
  have hleft : reflect d ((1 - C z * X) * A) =
      (X - C z) * reflect (d - 1) A := by
    conv_lhs => rw [hd]
    rw [reflect_mul _ _ hf hAn']
    simp [reflect_sub, reflect_one]
  have hrev1 : revAt 2 1 = 1 := revAt_le (by decide : 1 ≤ 2)
  have hrev2 : revAt 2 2 = 0 := revAt_le (by decide : 2 ≤ 2)
  have hX : reflect 2 (X : Polynomial R) = X := by
    simpa only [pow_one, hrev1] using (reflect_monomial (R := R) 2 1)
  have hX2 : reflect 2 ((X : Polynomial R) ^ 2) = 1 := by
    simpa only [hrev2, pow_zero] using (reflect_monomial (R := R) 2 2)
  have hreflect (r : ι) : reflect 2 (q r) = X ^ 2 - C (a r) * X + C (c r) := by
    simp [q, reflect_sub, reflect_one, hX, hX2]
  have hright : reflect d (∏ r : ι, q r ^ N) =
      ∏ r : ι, (X ^ 2 - C (a r) * X + C (c r)) ^ N := by
    change reflect ((2 * N) * Finset.univ.card) (∏ r ∈ Finset.univ, q r ^ N) = _
    rw [reflect_product_bound _ _ _ (fun r _ => hqN r)]
    apply Finset.prod_congr rfl
    intro r _
    rw [reflect_power_bound _ _ _ (hq r), hreflect r]
  have heq : (X - C z) * reflect (d - 1) A =
      ∏ r : ι, (X ^ 2 - C (a r) * X + C (c r)) ^ N := by
    rw [← hleft, h, hright]
  have heval := congrArg (fun f : Polynomial R => f.eval z) heq
  simp only [eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul,
    eval_prod, eval_pow, eval_add] at heval
  obtain ⟨r, _, hr⟩ := Finset.prod_eq_zero_iff.mp heval.symm
  exact ⟨r, eq_zero_of_pow_eq_zero hr⟩
