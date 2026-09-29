-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_nineteen_q4_547_no_five
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-14T03:17:50.470673+00:00
-- url     : https://prove2.me/submissions/b46b7e8d-5402-48ee-ab19-a30db9de70a3

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_not_dvd_of_order_certificate

theorem solution (e : Nat) :
    ¬ 5 ∣ ∑ i ∈ Finset.range (2 * e + 1), 547 ^ i := by
  apply OddPerfectNumber.geom_sum_not_dvd_of_order_certificate
  intro h
  have hbase : (547 : ZMod 5) = (2 : ZMod 5) := by
    apply (ZMod.natCast_eq_natCast_iff' 547 2 5).2
    norm_num
  have hord4 : orderOf (547 : ZMod 5) = 4 := by
    rw [hbase]
    apply (orderOf_eq_iff (x := (2 : ZMod 5)) (by norm_num)).2
    constructor
    · decide
    · intro n hn hnpos
      interval_cases n
      · intro hEq
        exact ((by decide : ¬ ((2 : ZMod 5) ^ 1 = 1)) hEq).elim
      · intro hEq
        exact ((by decide : ¬ ((2 : ZMod 5) ^ 2 = 1)) hEq).elim
      · intro hEq
        exact ((by decide : ¬ ((2 : ZMod 5) ^ 3 = 1)) hEq).elim
  change orderOf (547 : ZMod 5) ∣ 2 * e + 1 at h
  rw [hord4] at h
  omega
