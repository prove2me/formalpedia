-- Prove2me | solution 1 for ThreeSum.WeightedGlobalArenaAllocation.capacity_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T22:07:40.23837+00:00
-- url     : https://prove2.me/submissions/d5b83119-8863-4769-b1bc-aa9d2b632360

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryArenaPrefixFootprints
import Definitions.Def_Submission_Weighted_Global_TernaryArenaAllocation

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalArenaAllocation
open WeightedGlobalArenaPrefixFootprints WeightedGlobalArenaLayout
open WeightedGlobalCoverGoodMaps
variable {p m F : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalArenaAllocation
theorem _root_.solution (D E x : ℕ) : 256*(D+1)≤capacity D E x := by
  have hh : 1≤(x+1)^E := Nat.one_le_pow _ _ (by omega)
  unfold capacity
  exact Nat.le_mul_of_pos_right _ hh
end ThreeSum.WeightedGlobalArenaAllocation
