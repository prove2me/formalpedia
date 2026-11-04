-- Prove2me | solution 1 for ThreeSum.TernaryCoverCapParameters.actual_edge_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:33:08.047508+00:00
-- url     : https://prove2.me/submissions/253dc38b-0c3b-4a7e-bec6-ac2aaac74b33

import Definitions.Def_Submission_ThreeSum_TernaryCoverFrequency
import Mathlib.Algebra.Order.Floor.Div
import Definitions.Def_Submission_ThreeSum_TernaryCoverCapParameters
import Theorems.Thm_ThreeSum_TernaryLocalParameters_fixedPi_space
import Theorems.Thm_ThreeSum_TernaryLocalParameters_fixedPi_total
import Theorems.Thm_ThreeSum_TernaryPartitionCount_fixed_edge_mass_lower
import Theorems.Thm_ThreeSum_TernaryTypeLowerBound_vertices_lower_bound


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverCapParameters
open TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryCoverGoodMaps TernaryCoverFrequency TernaryPartitionCount TernaryTypeLowerBound
namespace ThreeSum.TernaryCoverCapParameters
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
end ThreeSum.TernaryCoverCapParameters
