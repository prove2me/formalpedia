-- Prove2me | solution 1 for OddPerfectNumber.Kernel.cyclotomic_plus_prime_residue_mod_euler
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T22:24:15.796982+00:00
-- url     : https://prove2.me/submissions/b5588e8c-ce35-4b92-a21b-4b8778b4dc6e

import Mathlib

set_option autoImplicit false

theorem solution {p q : Nat} [Fact p.Prime] [Fact q.Prime]
    (hp : p.Prime) (hp2 : p != 2) (hp4 : p % 4 = 1) (hq3 : q != 3)
    (hqd : q ∣ p ^ 2 + p + 1) :
    legendreSym q p = 1 := by
  have hcast : ((p : ZMod q)) ^ 2 + (p : ZMod q) + 1 = 0 := by
    have h1 : ((p ^ 2 + p + 1 : ℕ) : ZMod q) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).mpr hqd
    push_cast at h1
    exact h1
  set x : ZMod q := (p : ZMod q) with hx
  have h3 : x ^ 3 = 1 := by linear_combination (x - 1) * hcast
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0] at h3
    norm_num at h3
  have hx0' : ((p : ℤ) : ZMod q) ≠ 0 := by exact_mod_cast hx0
  rw [legendreSym.eq_one_iff q hx0']
  refine ⟨x ^ 2, ?_⟩
  rw [Int.cast_natCast, ← hx]
  linear_combination (-x) * h3
