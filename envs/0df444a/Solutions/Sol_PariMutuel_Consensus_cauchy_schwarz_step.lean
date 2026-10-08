-- Prove2me | solution 1 for PariMutuel.Consensus.cauchy_schwarz_step
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T09:45:16.012031+00:00
-- url     : https://prove2.me/submissions/3b16e0b9-d955-44ed-a51f-9aff801016b3

import Mathlib

set_option autoImplicit false

theorem solution {n : ℕ} (π π' : Fin n → ℝ) (hπ : ∀ k, 0 < π k)
    (hπ' : ∀ k, 0 ≤ π' k) (hs : ∑ k, π k = 1) (hs' : ∑ k, π' k = 1)
    (h : ∑ k, π' k * π' k / π k ≤ 1) : π' = π := by
  have hterm : ∀ k, (π' k - π k) ^ 2 / π k = π' k * π' k / π k - 2 * π' k + π k := by
    intro k
    have hk : π k ≠ 0 := (hπ k).ne'
    field_simp
    ring
  have key : ∑ k, (π' k - π k) ^ 2 / π k = ∑ k, π' k * π' k / π k - 1 := by
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hs, hs']
    ring
  have hnn : ∀ k ∈ (Finset.univ : Finset (Fin n)), 0 ≤ (π' k - π k) ^ 2 / π k :=
    fun k _ => div_nonneg (sq_nonneg _) (hπ k).le
  have hle : ∑ k, (π' k - π k) ^ 2 / π k ≤ 0 := by linarith
  have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (le_antisymm hle (Finset.sum_nonneg hnn))
  funext k
  have hk := hz k (Finset.mem_univ k)
  rw [div_eq_zero_iff] at hk
  rcases hk with h1 | h1
  · have : π' k - π k = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 h1
    linarith
  · exact absurd h1 (hπ k).ne'
