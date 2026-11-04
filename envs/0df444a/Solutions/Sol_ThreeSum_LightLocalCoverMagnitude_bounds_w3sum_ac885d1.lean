-- Prove2me | solution 1 for ThreeSum.LightLocalCoverMagnitude.bounds_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:20:36.991112+00:00
-- url     : https://prove2.me/submissions/78fb8f15-c50d-41c5-a0b8-480341627964

import Definitions.Def_Submission_ThreeSum_LightLocalCoverLayout
import Definitions.Def_Submission_ThreeSum_LocalParameterBounds
import Definitions.Def_Submission_ThreeSum_LightLocalCoverMagnitude
import Theorems.Thm_ThreeSum_LightLocalCoverMagnitude_succ_pow_bound
import Definitions.Def_WeightedCache3SUM_Alias_89fc1eb5a06df42f
import Definitions.Def_WeightedCache3SUM_Alias_ec6f8129c3d22917
import Theorems.Thm_ThreeSum_LocalParameterBounds_prime_bound
import Theorems.Thm_ThreeSum_LocalParameterBounds_width_bound


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverMagnitude
open LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverLayout
namespace ThreeSum.LightLocalCoverMagnitude
theorem _root_.solution (h : ℕ) : Bounds h (magnitude h) := by
  have hs : 0 ≤ h*h := Nat.zero_le _
  have raise (e : ℕ) (he : e ≤ 600000*(h+1)^2) : 2^e ≤ magnitude h :=
    Nat.pow_le_pow_right (by decide) he
  have hp := LocalParameterBounds.prime_bound h
  have hN : rows h ≤ 2^((514*h+2)*(2*(512*h))) := by
    unfold rows
    calc
      _ ≤ (2^(514*h+2))^(2*(512*h)) := Nat.pow_le_pow_left hp _
      _ = _ := by rw [← pow_mul]
  have hP : (localPrime h)^(2*(512*h)+1) ≤ 2^((514*h+2)*(2*(512*h)+1)) := by
    calc
      _ ≤ (2^(514*h+2))^(2*(512*h)+1) := Nat.pow_le_pow_left hp _
      _ = _ := by rw [← pow_mul]
  refine ⟨by exact Nat.two_pow_pos _,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (LocalParameterBounds.width_bound h).trans (raise _ (by nlinarith only [hs]))
  · have hv : LightLocalCoverLayout.vertices h ≤ 2^(512*h) := Nat.choose_le_two_pow _ _
    exact (succ_pow_bound hv).trans (raise _ (by nlinarith only [hs]))
  · exact (succ_pow_bound hp).trans (raise _ (by nlinarith only [hs]))
  · exact (succ_pow_bound (cap_bound h)).trans (raise _ (by nlinarith only [hs]))
  · exact (succ_pow_bound hN).trans (raise _ (by nlinarith only [hs]))
  · exact (succ_pow_bound (rounds_bound h)).trans (raise _ (by nlinarith only [hs]))
  · exact (succ_pow_bound hP).trans (raise _ (by nlinarith only [hs]))
  · exact (succ_pow_bound (le_rfl : 2^(512*h+1) ≤ 2^(512*h+1))).trans
      (raise _ (by nlinarith only [hs]))
end ThreeSum.LightLocalCoverMagnitude
