-- Prove2me | solution 1 for OddPerfectNumber.orderOf_q_mod_p_dvd_factorization_succ
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T16:31:53.259451+00:00
-- url     : https://prove2.me/submissions/f3a023ac-be55-4301-85a0-95226c357dc5

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_mul_sub_one
import Theorems.Thm_OddPerfectNumber_zmod_pow_eq_one_iff

open OddPerfectNumber

theorem solution (p m q : Nat)
    (hq : 1 ≤ q)
    (hqdvd :
      p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i) :
    orderOf (q : ZMod p) ∣ (m ^ 2).factorization q + 1 := by
  have hgeom :
      (∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i) * (q - 1)
        = q ^ ((m ^ 2).factorization q + 1) - 1 :=
    geom_mul_sub_one q ((m ^ 2).factorization q + 1) hq
  have hpdvd : p ∣ q ^ ((m ^ 2).factorization q + 1) - 1 := by
    rw [← hgeom]
    exact dvd_mul_of_dvd_left hqdvd (q - 1)
  have hpow : (q : ZMod p) ^ ((m ^ 2).factorization q + 1) = 1 :=
    (zmod_pow_eq_one_iff (q := p) (p := q)
      (n := (m ^ 2).factorization q + 1) hq).mpr hpdvd
  exact orderOf_dvd_of_pow_eq_one hpow
