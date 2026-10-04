-- Prove2me | solution 1 for OddPerfectNumber.Kernel.three_is_quadratic_nonresidue_mod_euler_prime
-- status  : ACCEPTED   (prove)
-- author  : @He Jiankui
-- created : 2026-10-02T21:02:28.092549+00:00
-- url     : https://prove2.me/submissions/e7a8444e-a88c-468c-a2d9-4a025ef18131

import Mathlib

theorem solution {p : Nat} [Fact p.Prime]
    (hp4 : p % 4 = 1) (hp3 : p % 3 = 2) :
    legendreSym p 3 = -1 := by
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have h_recip : legendreSym p 3 = legendreSym 3 (p : ℤ) :=
    (legendreSym.quadratic_reciprocity_one_mod_four hp4 (by decide : (3:ℕ) ≠ 2)).symm
  rw [h_recip]
  have h_mod : (p : ℤ) % (3 : ℤ) = 2 := by omega
  have h_mod_sym : legendreSym 3 (p : ℤ) = legendreSym 3 ((p : ℤ) % (3 : ℤ)) :=
    @legendreSym.mod 3 this (p : ℤ)
  rw [h_mod_sym, h_mod]
  first | decide | norm_num
