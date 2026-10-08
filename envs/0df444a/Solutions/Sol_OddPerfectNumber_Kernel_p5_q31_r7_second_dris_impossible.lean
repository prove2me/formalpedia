-- Prove2me | solution 1 for OddPerfectNumber.Kernel.p5_q31_r7_second_dris_impossible
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T11:59:18.660966+00:00
-- url     : https://prove2.me/submissions/a77f5751-bbe0-4012-b2e9-89aa73a560fd

import Mathlib

theorem solution (m d1 : Nat)
    (hd1 : 0 < d1) (hm : m = 651 * d1)
    (h2 : (∑ d ∈ (m ^ 2).divisors, d) =
      5 ^ 5 * (d1 ^ 2 * (31 * 7))) :
    False := by
  let D : Finset Nat :=
    {423801, 141267, 60543, 20181, 13671, 8649, 6727, 4557}
  let f : Nat → Nat := fun d => d1 ^ 2 * d
  have hm0 : m ≠ 0 := by
    rw [hm]
    positivity
  have hbase : 651 ^ 2 ∣ m ^ 2 := by
    refine ⟨d1 ^ 2, ?_⟩
    rw [hm]
    ring
  have hscale : ∀ d, d ∣ 651 ^ 2 → f d ∣ m ^ 2 := by
    intro d hd
    have hmul : d1 ^ 2 * d ∣ d1 ^ 2 * 651 ^ 2 :=
      Nat.mul_dvd_mul_left (d1 ^ 2) hd
    have heq : d1 ^ 2 * 651 ^ 2 = m ^ 2 := by
      rw [hm]
      ring
    rw [heq] at hmul
    exact hmul
  have hDsub : D ⊆ (651 ^ 2).divisors := by
    intro d hd
    simp [D] at hd
    rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      apply Nat.mem_divisors.mpr
      constructor
      · norm_num
      · norm_num
  have hinj : Set.InjOn f (D : Set Nat) := by
    intro x hx y hy hxy
    dsimp [f] at hxy
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hd1 2) hxy
  have himage : D.image f ⊆ (m ^ 2).divisors := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨d, hd, rfl⟩
    exact Nat.mem_divisors.mpr ⟨hscale d ((Nat.mem_divisors.mp (hDsub hd)).1),
      pow_ne_zero 2 hm0⟩
  have hsum : (∑ z ∈ D.image f, z) = d1 ^ 2 * 679396 := by
    rw [Finset.sum_image hinj]
    norm_num [f, D, Finset.mul_sum] <;> ring
  have hle : d1 ^ 2 * 679396 ≤ ∑ d ∈ (m ^ 2).divisors, d := by
    rw [← hsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg himage (by
      intro x hx hnot
      exact Nat.zero_le _)
  rw [h2] at hle
  norm_num at hle
  have hle' : d1 ^ 2 * 679396 ≤ 678125 * d1 ^ 2 := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hle
  have hpos : 0 < d1 ^ 2 := pow_pos hd1 2
  have hbad : 678125 * d1 ^ 2 < d1 ^ 2 * 679396 := by
    calc
      678125 * d1 ^ 2 < 679396 * d1 ^ 2 :=
        Nat.mul_lt_mul_of_pos_right (by norm_num) hpos
      _ = d1 ^ 2 * 679396 := by ring
  exact (Nat.not_le_of_gt hbad) hle'
