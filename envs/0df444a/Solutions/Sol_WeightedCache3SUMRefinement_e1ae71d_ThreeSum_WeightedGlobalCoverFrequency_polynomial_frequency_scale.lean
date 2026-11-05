-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverFrequency.polynomial_frequency_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:35:42.080104+00:00
-- url     : https://prove2.me/submissions/f802a95b-4e70-4f16-8a74-a99ea9940748

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverGoodMaps
import Definitions.Def_Submission_ThreeSum_Greedy
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryPartitionCount
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverFrequency
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalPartitionCount_fixed_prime_sq_le_poly_edges


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverFrequency
open Finset TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open WeightedGlobalCoverGoodMaps
open scoped BigOperators
variable (m p : ℕ) [Fact p.Prime]
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverFrequency
theorem _root_.solution
    (hup : p^2 ≤ 16*(vertices (fixedLength m) (fixedPi m)).card*
      (2^(fixedPi m 1)*3^(fixedPi m 2))) :
    4*p^4*3^16 ≤ frequencyFactor m*Fintype.card (ActualEdge m)^2 := by
  have h := WeightedGlobalPartitionCount.fixed_prime_sq_le_poly_edges m p hup
  have hs := Nat.mul_le_mul_left (4*3^16) (Nat.pow_le_pow_left h 2)
  unfold frequencyFactor
  change 4*p^4*3^16 ≤
    4*3^16*(16*WeightedGlobalPartitionCount.partitionLoss (2379766416784020*m) (292929977780940*m))^2*
      Fintype.card (LocalEdge (fixedLength m) (fixedAlpha m) (fixedPi m))^2
  convert hs using 1 <;> ring
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverFrequency
