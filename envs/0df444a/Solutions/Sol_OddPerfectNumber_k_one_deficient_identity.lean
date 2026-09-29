-- Prove2me | solution 1 for OddPerfectNumber.k_one_deficient_identity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T19:57:17.309727+00:00
-- url     : https://prove2.me/submissions/79543506-7a8a-47af-b777-8e8631da73a1

import Mathlib

theorem solution (p m d : Nat)
    (hp4 : p % 4 = 1)
    (hdvd : m ^ 2 = ((p + 1) / 2) * d)
    (hsig : (∑ x ∈ (m ^ 2).divisors, x) = p * d) :
    2 * m ^ 2 = (∑ x ∈ (m ^ 2).divisors, x) + d := by
  have hhalf : 2 * ((p + 1) / 2) = p + 1 := by
    omega
  calc
    2 * m ^ 2 = 2 * (((p + 1) / 2) * d) := by rw [hdvd]
    _ = (2 * ((p + 1) / 2)) * d := by ring
    _ = (p + 1) * d := by rw [hhalf]
    _ = p * d + d := by ring
    _ = (∑ x ∈ (m ^ 2).divisors, x) + d := by rw [hsig]
