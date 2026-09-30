-- Prove2me | solution 1 for Smooth4Laurent.mass_two_positive
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T06:14:23.005578+00:00
-- url     : https://prove2.me/submissions/f6849d87-595c-466d-94ac-9874a8dc16a7

import Mathlib
set_option autoImplicit false
open scoped BigOperators
namespace AlgebraContinuationTwo
private theorem extend_block (w : ℤ →₀ ℤ) (hOne : ∀ j : ℤ, 0 ≤ w j + w (j - 1))
    (a b : ℤ) (hab : a ≤ b) :
    (∑ k ∈ Finset.Icc a b, w k) ≤ ∑ k ∈ Finset.Icc (a - 2) (b + 2), w k := by
  classical
  have heq : Finset.Icc (a - 2) (b + 2) =
      {a - 2, a - 1} ∪ (Finset.Icc a b ∪ {b + 1, b + 2}) := by
    ext x
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hd1 : Disjoint ({a - 2, a - 1} : Finset ℤ) (Finset.Icc a b ∪ {b + 1, b + 2}) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hx hy
    omega
  have hd2 : Disjoint (Finset.Icc a b) ({b + 1, b + 2} : Finset ℤ) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton] at hx hy
    omega
  rw [heq, Finset.sum_union hd1, Finset.sum_union hd2]
  rw [Finset.sum_pair (by omega : a - 2 ≠ a - 1), Finset.sum_pair (by omega : b + 1 ≠ b + 2)]
  have hL := hOne (a - 1)
  have hR := hOne (b + 2)
  have hLarg : a - 1 - 1 = a - 2 := by omega
  have hRarg : b + 2 - 1 = b + 1 := by omega
  rw [hLarg] at hL
  rw [hRarg] at hR
  omega

private theorem five_block_le_sum (w : ℤ →₀ ℤ)
    (hOne : ∀ j : ℤ, 0 ≤ w j + w (j - 1)) (j : ℤ) :
    (∑ k ∈ Finset.Icc (j - 2) (j + 2), w k) ≤ w.sum (fun _ a => a) := by
  classical
  have hGrow (n : ℕ) :
      (∑ k ∈ Finset.Icc (j - 2) (j + 2), w k) ≤
        ∑ k ∈ Finset.Icc (j - (2 * n + 2)) (j + (2 * n + 2)), w k := by
    induction n with
    | zero => simp
    | succ n ih =>
      have h := extend_block w hOne (j - (2 * n + 2)) (j + (2 * n + 2)) (by omega)
      convert le_trans ih h using 1 <;> congr 2 <;> push_cast <;> ring
  obtain ⟨N, hN⟩ := w.support.bddAbove
  obtain ⟨L, hL⟩ := w.support.bddBelow
  obtain ⟨n, hn⟩ := exists_nat_gt (max (N - j) (j - L))
  have hs : w.support ⊆ Finset.Icc (j - (2 * (n : ℤ) + 2)) (j + (2 * n + 2)) := by
    intro k hk
    have hu := hN hk
    have hl := hL hk
    simp only [Finset.mem_Icc]
    omega
  have heq : w.sum (fun _ a => a) =
      ∑ k ∈ Finset.Icc (j - (2 * (n : ℤ) + 2)) (j + (2 * n + 2)), w k := by
    exact Finsupp.sum_of_support_subset w hs (fun _ a => a) (by simp)
  rw [heq]
  exact hGrow n

private theorem negative_mass_ge_three
    (w : ℤ →₀ ℤ)
    (hOne : ∀ j : ℤ, 0 ≤ w j + w (j - 1))
    (hTwo : ∀ j : ℤ, 0 ≤ w j + w (j - 2))
    (hNegative : ∃ j : ℤ, w j < 0) :
    3 ≤ w.sum (fun _ a => a) := by
  classical
  obtain ⟨j, hj⟩ := hNegative
  have heq : Finset.Icc (j - 2) (j + 2) = {j - 2, j - 1, j, j + 1, j + 2} := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  have hB := five_block_le_sum w hOne j
  rw [heq] at hB
  have hA : j - 2 ∉ ({j - 1, j, j + 1, j + 2} : Finset ℤ) := by simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have hB' : j - 1 ∉ ({j, j + 1, j + 2} : Finset ℤ) := by simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  have hC : j ∉ ({j + 1, j + 2} : Finset ℤ) := by simp only [Finset.mem_insert, Finset.mem_singleton]; omega
  rw [Finset.sum_insert hA, Finset.sum_insert hB', Finset.sum_insert hC,
    Finset.sum_pair (by omega : j + 1 ≠ j + 2)] at hB
  have h1 := hOne j
  have h2 := hTwo j
  have h3 := hOne (j + 1)
  have h4 := hTwo (j + 2)
  simp only [show j + 1 - 1 = j by omega] at h3
  simp only [show j + 2 - 2 = j by omega] at h4
  omega
end AlgebraContinuationTwo

theorem solution
    (w : ℤ →₀ ℤ)
    (hOne : ∀ j : ℤ, 0 ≤ w j + w (j - 1))
    (hTwo : ∀ j : ℤ, 0 ≤ w j + w (j - 2))
    (hMass : w.sum (fun _ a => a) = 2) :
    ∀ j : ℤ, 0 ≤ w j := by
  intro j
  by_contra hj
  have hN : ∃ j : ℤ, w j < 0 := ⟨j, lt_of_not_ge hj⟩
  have h := AlgebraContinuationTwo.negative_mass_ge_three w hOne hTwo hN
  omega
#print axioms solution
