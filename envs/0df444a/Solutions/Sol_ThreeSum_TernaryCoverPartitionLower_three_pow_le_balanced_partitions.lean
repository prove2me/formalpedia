-- Prove2me | solution 1 for ThreeSum.TernaryCoverPartitionLower.three_pow_le_balanced_partitions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:00:23.037378+00:00
-- url     : https://prove2.me/submissions/42f6da95-b0ed-44c6-a17a-83e45e848119

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSum_TernaryCoverPartitionLower
import Theorems.Thm_ThreeSum_TernaryCoverPartitionLower_three_pow_le_weighted_choose
import Theorems.Thm_ThreeSum_LocalCoverBounds_groupSize_lower


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverPartitionLower
open BinomialEntropy LocalCoverBounds
namespace ThreeSum.TernaryCoverPartitionLower
theorem _root_.solution (s : ℕ) :
    3 ^ (3*s) ≤ (3*s+1)*(2*s+1)*((3*s).choose s*(2*s).choose s) := by
  have h2 := groupSize_lower s
  have h3 := three_pow_le_weighted_choose s
  calc
    _ ≤ (3*s+1)*(3*s).choose s*2^(2*s) := h3
    _ ≤ (3*s+1)*(3*s).choose s*((2*s+1)*(2*s).choose s) :=
      Nat.mul_le_mul_left _ h2
    _ = _ := by ring
end ThreeSum.TernaryCoverPartitionLower
