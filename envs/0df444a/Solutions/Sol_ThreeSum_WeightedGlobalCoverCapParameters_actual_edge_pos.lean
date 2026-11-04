-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCoverCapParameters.actual_edge_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:49:06.253955+00:00
-- url     : https://prove2.me/submissions/9baa9471-7d86-48ff-909c-72f52c01f355

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverFrequency
import Mathlib.Algebra.Order.Floor.Div
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Theorems.Thm_ThreeSum_TernaryTypeLowerBound_vertices_lower_bound
import Theorems.Thm_ThreeSum_WeightedGlobalLocalParameters_fixedPi_space
import Theorems.Thm_ThreeSum_WeightedGlobalLocalParameters_fixedPi_total
import Theorems.Thm_ThreeSum_WeightedGlobalPartitionCount_fixed_edge_mass_lower


set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalCoverCapParameters
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open WeightedGlobalCoverGoodMaps WeightedGlobalCoverFrequency WeightedGlobalPartitionCount TernaryTypeLowerBound
namespace ThreeSum.WeightedGlobalCoverCapParameters
theorem _root_.solution (m : ℕ) : 0 < Fintype.card (ActualEdge m) := by
  have hR : 0 < 2^(fixedPi m 1)*3^(fixedPi m 2) := by positivity
  have hM := hR.trans_le (vertices_lower_bound (fixedPi m) (fixedPi_total m) (fixedPi_space m))
  have hpos := Nat.mul_pos hM hR
  have hmass := fixed_edge_mass_lower m
  by_contra hn
  have hz : Fintype.card (ActualEdge m) = 0 := by omega
  change _ ≤ _*Fintype.card (ActualEdge m) at hmass
  rw [hz, mul_zero] at hmass
  omega
end ThreeSum.WeightedGlobalCoverCapParameters
