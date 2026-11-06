-- Prove2me | solution 1 for bounded_of_shift
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:31:13.271828+00:00
-- url     : https://prove2.me/submissions/41fb7d3a-78ea-4b75-9dd8-2da399fb1d15

import Definitions.Def_PrimeNumberTheoremAnd_Wiener

open Filter

theorem solution {u : ℕ → ℝ} (h : BoundedAtFilter atTop (shift u)) :
    BoundedAtFilter atTop u := by
  rw [BoundedAtFilter, Asymptotics.isBigO_iff] at h ⊢
  obtain ⟨C, hC⟩ := h
  refine ⟨C, ?_⟩
  rw [Filter.eventually_atTop] at hC ⊢
  obtain ⟨N, hN⟩ := hC
  refine ⟨N + 1, fun n hn => ?_⟩
  have hnpos : 1 ≤ n := by omega
  simpa [shift, Nat.sub_add_cancel hnpos] using hN (n - 1) (by omega)
