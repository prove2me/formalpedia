-- Prove2me | solution 1 for ThreeSum19202796.threeSum_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T06:15:56.791338+00:00
-- url     : https://prove2.me/submissions/1330a0f6-7fbb-434c-85ee-cc94041040dc

import Theorems.Thm_WeightedCache3SUM_bound_192027942

set_option autoImplicit false
set_option relaxedAutoImplicit false

private theorem runtime_bound_implication (T : Nat → Nat)
    (h : EndStatement.BigO T (96013971 / 50000000 : Rat)) :
    EndStatement.BigO T ((4800699 : Rat) / 2500000) := by
  unfold EndStatement.BigO at h ⊢
  simp only [show (96013971 / 50000000 : Rat).den = 50000000 from by decide +kernel,
    show (96013971 / 50000000 : Rat).num.toNat = 96013971 from by decide +kernel] at h
  simp only [show ((4800699 : Rat) / 2500000).den = 2500000 from by decide +kernel,
    show ((4800699 : Rat) / 2500000).num.toNat = 4800699 from by decide +kernel]
  obtain ⟨K, hK⟩ := h
  refine ⟨K + 1, ?_⟩
  intro n hn
  apply (Nat.pow_le_pow_iff_left (n := 20) (by decide)).mp
  calc
    (T n ^ 2500000) ^ 20 = T n ^ 50000000 := by
      rw [← Nat.pow_mul]
    _ ≤ K * n ^ 96013971 := hK n hn
    _ ≤ (K + 1) ^ 20 * n ^ 96013980 := by
      apply Nat.mul_le_mul
      · exact Nat.le_trans (Nat.le_succ K) (Nat.le_self_pow (by decide) (K + 1))
      · exact Nat.pow_le_pow_right (Nat.lt_of_lt_of_le (by decide : 0 < 2) hn) (by decide)
    _ = ((K + 1) * n ^ 4800699) ^ 20 := by
      rw [Nat.mul_pow, ← Nat.pow_mul]

theorem solution :
    EndStatement.ThreeSum.SolvedInTime ((4800699 : Rat) / 2500000) := by
  intro κ
  obtain ⟨P, b, T, hT, hCorrect⟩ := WeightedCache3SUM.bound_192027942 κ
  exact ⟨P, b, T, runtime_bound_implication T hT, hCorrect⟩
