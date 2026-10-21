-- Prove2me | solution 1 for ShipConsol.OneWH.lemma_E1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T14:29:25.612515+00:00
-- url     : https://prove2.me/submissions/6d217f84-4507-445c-a7b2-a5c001c50cf2

import Mathlib
set_option autoImplicit false

theorem solution (n : ℕ) (a b : Fin (n + 1) → ℝ) (hb : Antitone b) : Finset.univ.inf' Finset.univ_nonempty (fun i => a i + b i) - Finset.univ.inf' Finset.univ_nonempty a ≥ b (Fin.last n) := by
  rw [ge_iff_le, le_sub_iff_add_le, add_comm]
  rw [Finset.le_inf'_iff]
  intro i _
  have h1 : Finset.univ.inf' Finset.univ_nonempty a ≤ a i := Finset.inf'_le _ (Finset.mem_univ i)
  have h2 : b (Fin.last n) ≤ b i := hb (Fin.le_last i)
  linarith
