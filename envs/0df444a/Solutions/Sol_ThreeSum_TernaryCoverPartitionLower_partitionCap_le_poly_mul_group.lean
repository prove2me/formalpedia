-- Prove2me | solution 1 for ThreeSum.TernaryCoverPartitionLower.partitionCap_le_poly_mul_group
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:04:29.849322+00:00
-- url     : https://prove2.me/submissions/a45949eb-8061-4cba-aa10-2d8f83b56e8f

import Definitions.Def_Submission_ThreeSum_BinomialEntropy
import Definitions.Def_Submission_ThreeSum_LocalCoverBounds
import Definitions.Def_Submission_ThreeSum_TernaryCoverPartitionLower
import Theorems.Thm_ThreeSum_TernaryCoverPartitionLower_three_pow_le_balanced_partitions
import Theorems.Thm_ThreeSum_LayerCounts_mem_edgeSet
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
import Theorems.Thm_ThreeSum_LocalCoverBounds_groupSize_lower
attribute [local simp] ThreeSum.LayerCounts.mem_edgeSet
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverPartitionLower
open BinomialEntropy LocalCoverBounds
namespace ThreeSum.TernaryCoverPartitionLower
theorem _root_.solution (r s : ℕ) :
    2 ^ (2*r) * 3 ^ (3*s) ≤
      (2*r+1)*(3*s+1)*(2*s+1)*
        ((2*r).choose r * (3*s).choose s * (2*s).choose s) := by
  have h := Nat.mul_le_mul (groupSize_lower r) (three_pow_le_balanced_partitions s)
  simpa [groupSize, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
end ThreeSum.TernaryCoverPartitionLower
