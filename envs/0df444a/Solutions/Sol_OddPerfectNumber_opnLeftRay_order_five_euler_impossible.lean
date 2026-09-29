-- Prove2me | solution 1 for OddPerfectNumber.opnLeftRay_order_five_euler_impossible
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-19T10:30:45.26178+00:00
-- url     : https://prove2.me/submissions/e99908a8-d41b-4d3c-aa74-5e24dba162b0

import Mathlib
import Definitions.Def_opnLeftRay
import Theorems.Thm_OddPerfectNumber_opnLeftRay_mod_five_period_three

open OddPerfectNumber

theorem solution
    (p q k m : Nat)
    (hp : p.Prime)
    (hq : q.Prime)
    (hq_lt_p : q < p)
    (h5 : orderOf (q : ZMod p) = 5)
    (hpk : p + 1 = q * k)
    (hedge : q = opnLeftRay (3 * m) ∧ k = opnLeftRay (3 * m + 1)) :
    False := by
  have hmod := opnLeftRay_mod_five_period_three m
  have hqmod : q % 5 = 1 := by
    rw [hedge.1]
    exact hmod.1
  have hkmod : k % 5 = 1 := by
    rw [hedge.2]
    exact hmod.2.1
  have hmulmod := Nat.mul_mod q k 5
  rw [hqmod, hkmod] at hmulmod
  have hpmod : p % 5 = 0 := by
    omega
  have h5dvd : 5 ∣ p := Nat.dvd_of_mod_eq_zero hpmod
  have hp5 : p = 5 := by
    rcases hp.eq_one_or_self_of_dvd 5 h5dvd with h | h
    · norm_num at h
    · exact h.symm
  letI : Fact p.Prime := ⟨hp⟩
  have hq0 : (q : ZMod p) ≠ 0 := by
    intro hzero
    have hdiv : p ∣ q := (ZMod.natCast_eq_zero_iff q p).mp hzero
    rcases hq.eq_one_or_self_of_dvd p hdiv with h | h
    · omega
    · omega
  have hord := ZMod.orderOf_dvd_card_sub_one hq0
  rw [h5, hp5] at hord
  omega
