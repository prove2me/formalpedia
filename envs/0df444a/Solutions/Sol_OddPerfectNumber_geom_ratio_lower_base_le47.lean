-- Prove2me | solution 1 for OddPerfectNumber.geom_ratio_lower_base_le47
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T01:16:55.81112+00:00
-- url     : https://prove2.me/submissions/2b80cddc-3ec8-49b4-99db-012c5da456d5

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_last_two_terms_le

theorem solution (q e : Nat) (hq : q ≤ 47) (he : 2 ≤ e) :
    48 * q ^ e ≤ 47 * (∑ i ∈ Finset.range (e + 1), q ^ i) := by
  have hpow : q ^ e ≤ 47 * q ^ (e - 1) := by
    rw [show e = (e - 1) + 1 by omega, pow_succ]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left (q ^ (e - 1)) hq
  have hlin : 48 * q ^ e ≤ 47 * q ^ e + 47 * q ^ (e - 1) := by
    omega
  have htwo := OddPerfectNumber.geom_sum_last_two_terms_le q e (by omega)
  have hmul := Nat.mul_le_mul_left 47 htwo
  calc
    48 * q ^ e ≤ 47 * q ^ e + 47 * q ^ (e - 1) := hlin
    _ = 47 * (q ^ e + q ^ (e - 1)) := by ring
    _ ≤ 47 * (∑ i ∈ Finset.range (e + 1), q ^ i) := hmul
