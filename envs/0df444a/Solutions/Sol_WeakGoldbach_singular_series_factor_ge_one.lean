-- Prove2me | solution 1 for WeakGoldbach.singular_series_factor_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T22:53:03.208704+00:00
-- url     : https://prove2.me/submissions/7cb043b3-076b-4e9b-84bd-0334ce4c84b4

import Mathlib

theorem solution (n : ℕ) :
    1 ≤ ∏ p ∈ n.primeFactors.filter (2 < ·), ((p : ℝ) - 1) / ((p : ℝ) - 2) := by
  apply Finset.one_le_prod
  intro p hp
  rw [Finset.mem_filter] at hp
  obtain ⟨hpf, hp2⟩ := hp
  have hpP : Nat.Prime p := (Nat.mem_primeFactors.mp hpf).1
  have h2 : (2 : ℝ) < p := by exact_mod_cast hp2
  rw [one_le_div (by linarith)]
  linarith
