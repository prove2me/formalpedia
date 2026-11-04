-- Prove2me | solution 1 for ThreeSum.WeightedModuli.joint_le_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:38:59.075011+00:00
-- url     : https://prove2.me/submissions/0667e745-9bf8-430a-85a5-e9e48162f33e

import Definitions.Def_Submission_ThreeSum_Auxiliary
import Definitions.Def_Submission_ThreeSum_WeightedModuli

set_option autoImplicit false
open ThreeSum ThreeSum.WeightedModuli
open Finset Arithmetic
open scoped BigOperators
namespace ThreeSum.WeightedModuli
theorem _root_.solution (q p : ℕ) (hp : 1 ≤ p) : joint q p ≤ q * p := by
  unfold joint
  split
  · exact Nat.le_mul_of_pos_right q hp
  · exact le_rfl
end ThreeSum.WeightedModuli
