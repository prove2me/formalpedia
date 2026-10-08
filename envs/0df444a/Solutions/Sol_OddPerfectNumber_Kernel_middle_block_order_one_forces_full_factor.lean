-- Prove2me | solution 1 for OddPerfectNumber.Kernel.middle_block_order_one_forces_full_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T10:26:14.333199+00:00
-- url     : https://prove2.me/submissions/a946eeed-9458-4a86-9255-5a14bc7061a6

import Mathlib

theorem solution (p q k : Nat) (hp : p.Prime) (hq : q.Prime)
    (hC : p ^ 2 + p + 1 = q * k)
    (hqmod : q % p = 1) (hkmod : k % p = 1) :
    q = p ^ 2 + p + 1 := by
  have hp0 : 0 < p := hp.pos
  have hmod_ge : ∀ x : Nat, x % p = 1 → 2 ≤ x → p + 1 ≤ x := by
    intro x hx hx2
    by_cases hlt : x < p
    · have hxm : x % p = x := Nat.mod_eq_of_lt hlt
      omega
    · have hxp : p ≤ x := by omega
      by_cases heq : x = p
      · subst x
        norm_num at hx
      · omega
  have hqge : p + 1 ≤ q := hmod_ge q hqmod hq.two_le
  by_cases hk1 : k = 1
  · rw [hk1] at hC
    simpa [mul_one] using hC.symm
  · have hk2 : 2 ≤ k := by
      have hk0 : 0 < k := by
        by_cases hklt : k < p
        · have hkm := Nat.mod_eq_of_lt hklt
          omega
        · omega
      omega
    have hkge : p + 1 ≤ k := hmod_ge k hkmod hk2
    have hlow : (p + 1) ^ 2 ≤ q * k := by
      nlinarith
    have hupp : q * k < (p + 1) ^ 2 := by
      rw [← hC]
      nlinarith
    omega
