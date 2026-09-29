-- Prove2me | solution 1 for OddPerfectNumber.q2_five_q3_twentythree_q4_61_external_131_source_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-15T04:00:16.36313+00:00
-- url     : https://prove2.me/submissions/213214f0-eed4-46b2-92f9-a5fd1f301937

import Mathlib

theorem solution (e : Nat) (he : 5 ∣ 2 * e + 1) :
    131 ∣ ∑ i ∈ Finset.range (2 * e + 1), 61 ^ i := by
  obtain ⟨k, hk⟩ := he
  have hfive : 131 ∣ ∑ i ∈ Finset.range 5, 61 ^ i := by
    norm_num
  have hblock : ∀ t : Nat, 131 ∣ ∑ i ∈ Finset.range (5 * t), 61 ^ i := by
    intro t
    induction t with
    | zero => simp
    | succ t iht =>
        rw [show 5 * (t + 1) = 5 * t + 5 by omega]
        rw [Finset.sum_range_add]
        have hshift :
            (∑ i ∈ Finset.range 5, 61 ^ (5 * t + i)) =
              61 ^ (5 * t) * (∑ i ∈ Finset.range 5, 61 ^ i) := by
          simp_rw [pow_add]
          rw [Finset.mul_sum]
        rw [hshift]
        exact dvd_add iht (dvd_mul_of_dvd_right hfive _)
  rw [hk]
  exact hblock k
