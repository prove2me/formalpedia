-- Prove2me | solution 1 for OddPerfectNumber.orderOf_ge_five_and_eq_five_package
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-18T16:39:30.64283+00:00
-- url     : https://prove2.me/submissions/99cf35ea-c8f6-4130-8799-dd672374978c

import Mathlib
import Theorems.Thm_OddPerfectNumber_three_mul_half_factorization_le_order_sub_one
import Theorems.Thm_OddPerfectNumber_orderOf_q_mod_p_dvd_factorization_succ
import Theorems.Thm_OddPerfectNumber_sq_factorization_two

open OddPerfectNumber

theorem solution (p m q : Nat)
    (hp : p.Prime)
    (hp4 : p % 4 = 1)
    (hq : q.Prime)
    (hqdvd :
      p ∣ ∑ i ∈ Finset.range ((m ^ 2).factorization q + 1), q ^ i)
    (hqt : q ∣ (p + 1) / 2) :
    5 ≤ orderOf (q : ZMod p) ∧
      (orderOf (q : ZMod p) = 5 →
        ((p + 1) / 2).factorization q = 1 ∧
          (m ^ 2).factorization q % 5 = 4) := by
  have htpos : 0 < (p + 1) / 2 := by
    have h2 : 2 ≤ p := hp.two_le
    omega
  have htne : (p + 1) / 2 ≠ 0 := htpos.ne'
  have hb1 : 1 ≤ ((p + 1) / 2).factorization q :=
    hq.factorization_pos_of_dvd htne hqt
  have h3 : 3 * ((p + 1) / 2).factorization q ≤ orderOf (q : ZMod p) - 1 :=
    three_mul_half_factorization_le_order_sub_one p q hp hp4 hq hqt
  have hdvd : orderOf (q : ZMod p) ∣ (m ^ 2).factorization q + 1 :=
    orderOf_q_mod_p_dvd_factorization_succ p m q hq.one_le hqdvd
  have hafac : (m ^ 2).factorization q = 2 * m.factorization q :=
    sq_factorization_two (m := m) (q := q)
  have hodd : Odd ((m ^ 2).factorization q + 1) := by
    rw [hafac]
    exact ⟨m.factorization q, rfl⟩
  have hhodd : Odd (orderOf (q : ZMod p)) := hodd.of_dvd_nat hdvd
  have h4 : 4 ≤ orderOf (q : ZMod p) := by omega
  refine ⟨?_, ?_⟩
  · obtain ⟨k, hk⟩ := hhodd
    omega
  · intro h5
    have h5dvd : 5 ∣ (m ^ 2).factorization q + 1 := by
      rw [← h5]
      exact hdvd
    exact ⟨by omega, by omega⟩
