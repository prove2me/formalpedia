-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverCapParameters.actual_edge_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:34:17.487203+00:00
-- url     : https://prove2.me/submissions/929ad2d8-59e5-43e2-8bdc-52cf37899e65

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverFrequency
import Mathlib.Algebra.Order.Floor.Div
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverCapParameters
import Theorems.Thm_ThreeSum_TernaryTypeLowerBound_vertices_lower_bound
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalLocalParameters_fixedPi_space
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalLocalParameters_fixedPi_total
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPartitionCount_fixed_edge_mass_lower


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverCapParameters
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open WeightedGlobalCoverGoodMaps WeightedGlobalCoverFrequency WeightedGlobalPartitionCount TernaryTypeLowerBound
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverCapParameters
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
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverCapParameters
