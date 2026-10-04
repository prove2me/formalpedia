-- Prove2me | solution 2 for OddPerfectNumber.Kernel.five_euler_prime_is_five_mod_forty_eight
-- status  : ACCEPTED   (prove)
-- author  : @He Jiankui
-- created : 2026-10-02T21:01:38.18404+00:00
-- url     : https://prove2.me/submissions/60dd7480-b292-473b-a19a-476fc7658719

import Mathlib

theorem solution (p u : Nat) (hp4 : p % 4 = 1)
    (hshape : p + 1 = 6 * u ^ 2) :
    p % 48 = 5 := by
  have hu_rem2 : (u % 2 = 0) ∨ (u % 2 = 1) := by omega
  have hu_odd : u % 2 = 1 := by
    rcases hu_rem2 with h0 | h1
    · have hu_decomp : u = 2 * (u / 2) := by omega
      set q := u / 2
      have h_sq : 6 * u ^ 2 = 4 * (6 * q ^ 2) := by
        calc 6 * u ^ 2 = 6 * (2 * q) ^ 2 := by rw [hu_decomp]
        _ = 4 * (6 * q ^ 2) := by ring
      have h_p1_mod4 : (p + 1) % 4 = 0 := by
        have h_p1 : p + 1 = 4 * (6 * q ^ 2) := by
          rw [hshape, h_sq]
        rw [h_p1]
        exact Nat.mul_mod_right 4 (6 * q ^ 2)
      omega
    · exact h1
  have hr_cases : u % 8 = 1 ∨ u % 8 = 3 ∨ u % 8 = 5 ∨ u % 8 = 7 := by omega
  set k := u / 8
  have hu_decomp : u = 8 * k + (u % 8) := (Nat.div_add_mod u 8).symm
  rcases hr_cases with h1 | h3 | h5 | h7
  · have hu : u = 8 * k + 1 := by omega
    set M := 8 * k ^ 2 + 2 * k
    have h_alg : 6 * u ^ 2 = 48 * M + 6 := by
      calc 6 * u ^ 2 = 6 * (8 * k + 1) ^ 2 := by rw [hu]
      _ = 48 * M + 6 := by ring
    have h_p1 : p + 1 = 48 * M + 6 := by
      rw [hshape, h_alg]
    omega
  · have hu : u = 8 * k + 3 := by omega
    set M := 8 * k ^ 2 + 6 * k + 1
    have h_alg : 6 * u ^ 2 = 48 * M + 6 := by
      calc 6 * u ^ 2 = 6 * (8 * k + 3) ^ 2 := by rw [hu]
      _ = 48 * M + 6 := by ring
    have h_p1 : p + 1 = 48 * M + 6 := by
      rw [hshape, h_alg]
    omega
  · have hu : u = 8 * k + 5 := by omega
    set M := 8 * k ^ 2 + 10 * k + 3
    have h_alg : 6 * u ^ 2 = 48 * M + 6 := by
      calc 6 * u ^ 2 = 6 * (8 * k + 5) ^ 2 := by rw [hu]
      _ = 48 * M + 6 := by ring
    have h_p1 : p + 1 = 48 * M + 6 := by
      rw [hshape, h_alg]
    omega
  · have hu : u = 8 * k + 7 := by omega
    set M := 8 * k ^ 2 + 14 * k + 6
    have h_alg : 6 * u ^ 2 = 48 * M + 6 := by
      calc 6 * u ^ 2 = 6 * (8 * k + 7) ^ 2 := by rw [hu]
      _ = 48 * M + 6 := by ring
    have h_p1 : p + 1 = 48 * M + 6 := by
      rw [hshape, h_alg]
    omega
