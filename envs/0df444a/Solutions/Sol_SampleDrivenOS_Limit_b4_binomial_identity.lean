-- Prove2me | solution 1 for SampleDrivenOS.Limit.b4_binomial_identity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:23:50.021695+00:00
-- url     : https://prove2.me/submissions/2eb7e640-75ef-44dd-8f9a-fcbc8f0e160c

import Mathlib
set_option autoImplicit false

theorem solution (j : ℕ) (hj : 1 ≤ j) (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
    ∑ ℓ ∈ Finset.Icc 1 j, ((j - 1).choose (ℓ - 1) : ℝ) * (1 - t) ^ (j - ℓ) * t ^ ℓ = t := by
  obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
  have h1 : Finset.Icc 1 (n + 1) = Finset.Ico 1 (n + 2) := rfl
  rw [h1, Finset.sum_Ico_eq_sum_range]
  have h2 : (n + 2 - 1) = n + 1 := rfl
  rw [h2]
  have h3 : ∀ m ∈ Finset.range (n + 1),
      ((n + 1 - 1).choose (1 + m - 1) : ℝ) * (1 - t) ^ (n + 1 - (1 + m)) * t ^ (1 + m)
        = t * (t ^ m * (1 - t) ^ (n - m) * (n.choose m : ℝ)) := by
    intro m hm
    have hm' : m ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have e1 : n + 1 - 1 = n := rfl
    have e2 : 1 + m - 1 = m := by omega
    have e3 : n + 1 - (1 + m) = n - m := by omega
    rw [e1, e2, e3, pow_add]
    ring
  rw [Finset.sum_congr rfl h3, ← Finset.mul_sum, ← add_pow t (1 - t) n]
  simp
