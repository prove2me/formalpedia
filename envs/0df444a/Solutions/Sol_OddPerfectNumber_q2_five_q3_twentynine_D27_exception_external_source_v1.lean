-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_twentynine_D27_exception_external_source_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T14:51:56.623305+00:00
-- url     : https://prove2.me/submissions/9b3fc828-e770-4a79-95e8-64cec7a27802

import Mathlib
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_order_47_89_mod_53_eq_13
import Theorems.Thm_OddPerfectNumber_geom_sum_dvd_implies_order_dvd
import Theorems.Thm_OddPerfectNumber_q2_five_q3_twentynine_phi13_certificates

theorem solution (e q4 : Nat)
    (hdiv : 53 ∣ ∑ i ∈ Finset.range (2*e + 1), q4 ^ i)
    (hcases : q4 = 47 ∨ q4 = 89) :
    (q4 = 47 ∧ 2237 ∣ ∑ i ∈ Finset.range (2*e + 1), q4 ^ i) ∨
      (q4 = 89 ∧ 79 ∣ ∑ i ∈ Finset.range (2*e + 1), q4 ^ i) := by
  rcases hcases with h47 | h89
  · subst q4
    have hlen : orderOf (47 : ZMod 53) ∣ 2*e + 1 :=
      OddPerfectNumber.geom_sum_dvd_implies_order_dvd hdiv
    have h13 : 13 ∣ 2*e + 1 := by
      simpa [OddPerfectNumber.q2_five_q3_twentynine_order_47_89_mod_53_eq_13.1] using hlen
    rcases h13 with ⟨k, hk⟩
    have hblock : 2237 ∣ ∑ i ∈ Finset.range 13, 47 ^ i := by
      exact OddPerfectNumber.q2_five_q3_twentynine_phi13_certificates.1
    have hlocal : 2237 ∣ ∑ i ∈ Finset.range (13*k), 47 ^ i := by
      have hblocklift : ∀ j : Nat, 2237 ∣ ∑ i ∈ Finset.range (13*j), 47 ^ i := by
        intro j
        induction j with
        | zero => simp
        | succ j ih =>
            rw [Nat.mul_succ, Finset.sum_range_add]
            have hshift :
                (∑ x ∈ Finset.range 13, 47 ^ (13*j + x)) =
                  47 ^ (13*j) * (∑ x ∈ Finset.range 13, 47 ^ x) := by
              simp [pow_add, Finset.mul_sum, Nat.add_comm, Nat.add_left_comm,
                Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
            rw [hshift]
            exact dvd_add ih (dvd_mul_of_dvd_right hblock _)
      exact hblocklift k
    left
    exact ⟨rfl, by simpa [hk] using hlocal⟩
  · subst q4
    have hlen : orderOf (89 : ZMod 53) ∣ 2*e + 1 :=
      OddPerfectNumber.geom_sum_dvd_implies_order_dvd hdiv
    have h13 : 13 ∣ 2*e + 1 := by
      simpa [OddPerfectNumber.q2_five_q3_twentynine_order_47_89_mod_53_eq_13.2] using hlen
    rcases h13 with ⟨k, hk⟩
    have hblock : 79 ∣ ∑ i ∈ Finset.range 13, 89 ^ i := by
      exact OddPerfectNumber.q2_five_q3_twentynine_phi13_certificates.2
    have hlocal : 79 ∣ ∑ i ∈ Finset.range (13*k), 89 ^ i := by
      have hblocklift : ∀ j : Nat, 79 ∣ ∑ i ∈ Finset.range (13*j), 89 ^ i := by
        intro j
        induction j with
        | zero => simp
        | succ j ih =>
            rw [Nat.mul_succ, Finset.sum_range_add]
            have hshift :
                (∑ x ∈ Finset.range 13, 89 ^ (13*j + x)) =
                  89 ^ (13*j) * (∑ x ∈ Finset.range 13, 89 ^ x) := by
              simp [pow_add, Finset.mul_sum, Nat.add_comm, Nat.add_left_comm,
                Nat.add_assoc, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
            rw [hshift]
            exact dvd_add ih (dvd_mul_of_dvd_right hblock _)
      exact hblocklift k
    right
    exact ⟨rfl, by simpa [hk] using hlocal⟩
