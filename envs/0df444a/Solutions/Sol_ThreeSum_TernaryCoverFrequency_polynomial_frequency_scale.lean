-- Prove2me | solution 1 for ThreeSum.TernaryCoverFrequency.polynomial_frequency_scale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:37:28.052891+00:00
-- url     : https://prove2.me/submissions/8b439db2-06d3-496c-b2aa-3b391ae77436

import Definitions.Def_Submission_ThreeSum_TernaryCoverGoodMaps
import Definitions.Def_Submission_ThreeSum_Greedy
import Definitions.Def_Submission_ThreeSum_TernaryPartitionCount
import Definitions.Def_Submission_ThreeSum_TernaryCoverFrequency
import Theorems.Thm_ThreeSum_TernaryPartitionCount_fixed_prime_sq_le_poly_edges


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverFrequency
open Finset TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryCoverGoodMaps
open scoped BigOperators
variable (m p : ℕ) [Fact p.Prime]
namespace ThreeSum.TernaryCoverFrequency
theorem _root_.solution
    (hup : p^2 ≤ 16*(vertices (fixedLength m) (fixedPi m)).card*
      (2^(fixedPi m 1)*3^(fixedPi m 2))) :
    4*p^4*3^16 ≤ frequencyFactor m*Fintype.card (ActualEdge m)^2 := by
  have h := TernaryPartitionCount.fixed_prime_sq_le_poly_edges m p hup
  have hs := Nat.mul_le_mul_left (4*3^16) (Nat.pow_le_pow_left h 2)
  unfold frequencyFactor
  change 4*p^4*3^16 ≤
    4*3^16*(16*TernaryPartitionCount.partitionLoss (7930225*m) (978268*m))^2*
      Fintype.card (LocalEdge (fixedLength m) (fixedAlpha m) (fixedPi m))^2
  convert hs using 1 <;> ring
end ThreeSum.TernaryCoverFrequency
