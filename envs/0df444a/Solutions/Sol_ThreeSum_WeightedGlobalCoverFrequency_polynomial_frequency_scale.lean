-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCoverFrequency.polynomial_frequency_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:53:58.985218+00:00
-- url     : https://prove2.me/submissions/351f0441-2a9b-4379-b271-1b232e622eaa

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverGoodMaps
import Definitions.Def_Submission_ThreeSum_Greedy
import Definitions.Def_Submission_Weighted_Global_TernaryPartitionCount
import Definitions.Def_Submission_Weighted_Global_TernaryCoverFrequency
import Theorems.Thm_ThreeSum_WeightedGlobalPartitionCount_fixed_prime_sq_le_poly_edges


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCoverFrequency
open Finset TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open WeightedGlobalCoverGoodMaps
open scoped BigOperators
variable (m p : ℕ) [Fact p.Prime]
namespace ThreeSum.WeightedGlobalCoverFrequency
theorem _root_.solution
    (hup : p^2 ≤ 16*(vertices (fixedLength m) (fixedPi m)).card*
      (2^(fixedPi m 1)*3^(fixedPi m 2))) :
    4*p^4*3^16 ≤ frequencyFactor m*Fintype.card (ActualEdge m)^2 := by
  have h := WeightedGlobalPartitionCount.fixed_prime_sq_le_poly_edges m p hup
  have hs := Nat.mul_le_mul_left (4*3^16) (Nat.pow_le_pow_left h 2)
  unfold frequencyFactor
  change 4*p^4*3^16 ≤
    4*3^16*(16*WeightedGlobalPartitionCount.partitionLoss (2380004124000*m) (292746547000*m))^2*
      Fintype.card (LocalEdge (fixedLength m) (fixedAlpha m) (fixedPi m))^2
  convert hs using 1 <;> ring
end ThreeSum.WeightedGlobalCoverFrequency
