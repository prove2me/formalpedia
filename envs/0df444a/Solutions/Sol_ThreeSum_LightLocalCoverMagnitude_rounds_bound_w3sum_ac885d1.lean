-- Prove2me | solution 1 for ThreeSum.LightLocalCoverMagnitude.rounds_bound_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:05:30.534578+00:00
-- url     : https://prove2.me/submissions/4acf2351-814d-40e9-b7b7-124bf6eb97c3

import Definitions.Def_Submission_ThreeSum_LightLocalCoverLayout
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
import Definitions.Def_Submission_ThreeSum_LightLocalCoverMagnitude
import Theorems.Thm_ThreeSum_LightLocalCoverMagnitude_succ_pow_bound
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_ThreeSum_LocalParameterBounds_prime_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverMagnitude
open LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverLayout
namespace ThreeSum.LightLocalCoverMagnitude
theorem _root_.solution (h : ℕ) : scheduleSize h ≤ 2^(1029*h+16) := by
  have hp := LocalParameterBounds.prime_bound h
  have hp2 : localPrime h^2 ≤ 2^(2*(514*h+2)) := by
    calc
      _ ≤ (2^(514*h+2))^2 := Nat.pow_le_pow_left hp 2
      _ = _ := by rw [← pow_mul]; congr 1 <;> omega
  have hl : Nat.log2 (localPrime h^2) ≤ localPrime h^2 := by
    rw [Nat.log2_eq_log_two]
    exact Nat.log_le_self 2 _
  have hlog : Nat.log2 (localPrime h^2)+1 ≤ 2^(2*(514*h+2)+1) :=
    (Nat.add_le_add_right hl 1).trans (succ_pow_bound hp2)
  have hlin : 2*h+1 ≤ 2^(h+2) := by
    have hh := Nat.lt_two_pow_self (n := h)
    have hpow := Nat.two_pow_pos h
    rw [pow_add]
    norm_num
    omega
  calc
    scheduleSize h = 320*(2*h+1)*(Nat.log2 (localPrime h^2)+1) := rfl
    _ ≤ (2^9)*(2^(h+2))*(2^(2*(514*h+2)+1)) :=
      Nat.mul_le_mul (Nat.mul_le_mul (by decide) hlin) hlog
    _ = 2^(1029*h+16) := by
      rw [← pow_add,← pow_add]
      congr 1
      omega
end ThreeSum.LightLocalCoverMagnitude
