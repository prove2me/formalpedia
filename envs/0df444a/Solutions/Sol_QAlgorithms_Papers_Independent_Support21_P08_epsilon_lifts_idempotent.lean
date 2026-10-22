-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P08.epsilon_lifts_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T08:04:10.234005+00:00
-- url     : https://prove2.me/submissions/3163152a-3322-4e5e-be2d-1b45cd203fac

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P08
noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Support21.P08

open QAlgorithms.Papers.Independent.Renew46.P16 (CellIndex)

open QAlgorithms.Papers.Independent.Next46.P12 (PrimitiveIdempotent)

section RingAppendix

theorem g67d_eps_sum {C : Type*} [CommRing C] (N : ℕ) (hN : 1 ≤ N) (y : C) :
    epsilon N y + epsilon N (1 - y) = 1 := by
  have h1 : ((1 - y) + y) ^ (2 * N - 1) = 1 := by simp
  rw [add_pow] at h1
  have hn : 2 * N - 1 + 1 = N + N := by omega
  rw [hn, Finset.sum_range_add] at h1
  have hA : epsilon N y = ∑ x ∈ Finset.range N,
      (1 - y) ^ x * y ^ (2 * N - 1 - x) * ((2 * N - 1).choose x : C) := by
    unfold epsilon
    refine Finset.sum_congr rfl (fun i hi => ?_)
    ring
  have hB : epsilon N (1 - y) = ∑ x ∈ Finset.range N,
      (1 - y) ^ (N + x) * y ^ (2 * N - 1 - (N + x)) * ((2 * N - 1).choose (N + x) : C) := by
    unfold epsilon
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj' : j < N := Finset.mem_range.mp hj
    have e1 : 2 * N - 1 - (N - 1 - j) = N + j := by omega
    have e2 : 2 * N - 1 - (N + j) = N - 1 - j := by omega
    rw [e1, e2, sub_sub_cancel]
    have : Nat.choose (2 * N - 1) (N - 1 - j) = Nat.choose (2 * N - 1) (N + j) := by
      rw [← Nat.choose_symm (by omega : N - 1 - j ≤ 2 * N - 1), e1]
    rw [this]
    ring
  rw [hA, hB]
  exact h1

theorem g67d_eps_dvd {C : Type*} [CommRing C] (N : ℕ) (y : C) :
    y ^ N ∣ epsilon N y := by
  unfold epsilon
  refine Finset.dvd_sum (fun i hi => ?_)
  have hi' : i < N := Finset.mem_range.mp hi
  exact Dvd.dvd.mul_right (Dvd.dvd.mul_left (pow_dvd_pow y (by omega)) _) _

variable {H : Type*} [Ring H]

theorem g67d_aeval_eps (N : ℕ) (x : H) (p : Polynomial ℤ) :
    Polynomial.aeval x (epsilon N p) = epsilon N (Polynomial.aeval x p) := by
  simp [epsilon, map_sum, map_mul, map_pow, map_natCast, map_sub, map_one]

theorem solution (N : ℕ) (hN : 2 ≤ N) (I : AddSubgroup H)
    (hI : TwoSidedNilpotent I N) (x : H) (hx : x * x - x ∈ I) :
    epsilon N x * epsilon N x = epsilon N x ∧ epsilon N x - x ∈ I := by
  set φ := Polynomial.aeval (R := ℤ) x with hφ
  have hX : φ Polynomial.X = x := by simp [hφ]
  have he : epsilon N x = φ (epsilon N Polynomial.X) := by rw [g67d_aeval_eps, hX]
  have he' : epsilon N (1 - x) = φ (epsilon N (1 - Polynomial.X)) := by
    rw [g67d_aeval_eps]; simp [hφ]
  obtain ⟨a, ha⟩ := g67d_eps_dvd N (Polynomial.X : Polynomial ℤ)
  obtain ⟨b, hb⟩ := g67d_eps_dvd N (1 - Polynomial.X : Polynomial ℤ)
  have hsum := g67d_eps_sum N (by omega) (Polynomial.X : Polynomial ℤ)
  have hsumH : epsilon N x + epsilon N (1 - x) = 1 := by
    rw [he, he', ← map_add, hsum, map_one]
  have hxI : x * (1 - x) ∈ I := by
    have : x * (1 - x) = -(x * x - x) := by noncomm_ring
    rw [this]; exact I.neg_mem hx
  have hzero : (x * (1 - x)) ^ N = 0 := by
    rw [← List.prod_replicate]
    exact hI.2 _ (by simp) (fun y hy => by rw [List.eq_of_mem_replicate hy]; exact hxI)
  have hmap : φ (Polynomial.X * (1 - Polynomial.X)) = x * (1 - x) := by simp [hφ]
  refine ⟨?_, ?_⟩
  · have hprod : epsilon N x * epsilon N (1 - x) = 0 := by
      rw [he, he', ← map_mul, ha, hb]
      have : Polynomial.X ^ N * a * ((1 - Polynomial.X) ^ N * b) =
          (Polynomial.X * (1 - Polynomial.X)) ^ N * (a * b) := by rw [mul_pow]; ring
      rw [this, map_mul, map_pow, hmap, hzero, zero_mul]
    have : epsilon N x = epsilon N x * (epsilon N x + epsilon N (1 - x)) := by
      rw [hsumH, mul_one]
    calc epsilon N x * epsilon N x
        = epsilon N x * (epsilon N x + epsilon N (1 - x)) - epsilon N x * epsilon N (1 - x) := by
          noncomm_ring
      _ = epsilon N x := by rw [hprod, sub_zero, ← this]
  · have hpoly : epsilon N (Polynomial.X : Polynomial ℤ) - Polynomial.X =
        (Polynomial.X * (1 - Polynomial.X)) *
          (Polynomial.X ^ (N - 1) * a - (1 - Polynomial.X) ^ (N - 1) * b) := by
      have hN1 : N = (N - 1) + 1 := by omega
      have h2 : epsilon N (Polynomial.X : Polynomial ℤ) - Polynomial.X =
          epsilon N (Polynomial.X : Polynomial ℤ) * (1 - Polynomial.X) -
            Polynomial.X * epsilon N (1 - Polynomial.X) := by
        linear_combination (Polynomial.X : Polynomial ℤ) * hsum
      rw [h2]
      conv_lhs => rw [ha, hb, hN1]
      ring
    have : epsilon N x - x = (x * (1 - x)) *
        φ (Polynomial.X ^ (N - 1) * a - (1 - Polynomial.X) ^ (N - 1) * b) := by
      rw [he, ← hX, ← map_sub, hpoly, map_mul, hmap, hX]
    rw [this]
    exact (hI.1 _ _ hxI).2

end RingAppendix

end
