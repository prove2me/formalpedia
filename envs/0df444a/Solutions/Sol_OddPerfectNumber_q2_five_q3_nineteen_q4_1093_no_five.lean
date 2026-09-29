-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_nineteen_q4_1093_no_five
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T03:05:59.848494+00:00
-- url     : https://prove2.me/submissions/e64cfa2b-df28-4f10-8c3b-4e5cd9abff3d

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_order_certificate

theorem solution (e : Nat) :
    ¬ 5 ∣ ∑ i ∈ Finset.range (2 * e + 1), 1093 ^ i := by
  apply OddPerfectNumber.geom_sum_not_dvd_of_order_certificate
  intro h
  have hbase : (1093 : ZMod 5) = (3 : ZMod 5) := by
    apply (ZMod.natCast_eq_natCast_iff' 1093 3 5).2
    norm_num
  have hord4 : orderOf (1093 : ZMod 5) = 4 := by
    rw [hbase]
    apply (orderOf_eq_iff (x := (3 : ZMod 5)) (by norm_num)).2
    constructor
    · decide
    · intro n hn hnpos
      interval_cases n
      · intro hEq
        exact ((by decide : ¬ ((3 : ZMod 5) ^ 1 = 1)) hEq).elim
      · intro hEq
        exact ((by decide : ¬ ((3 : ZMod 5) ^ 2 = 1)) hEq).elim
      · intro hEq
        exact ((by decide : ¬ ((3 : ZMod 5) ^ 3 = 1)) hEq).elim
  change orderOf (1093 : ZMod 5) ∣ 2 * e + 1 at h
  rw [hord4] at h
  omega
