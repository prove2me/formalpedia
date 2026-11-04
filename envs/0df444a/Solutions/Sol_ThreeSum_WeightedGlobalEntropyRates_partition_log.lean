-- Prove2me | solution 1 for ThreeSum.WeightedGlobalEntropyRates.partition_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:48:07.26666+00:00
-- url     : https://prove2.me/submissions/0cb2757c-cfc6-4951-bdd8-f06b62024f71

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_GlobalParameters
import Definitions.Def_Submission_Weighted_Global_TernaryCoverScale
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalEntropyRates
open Filter Real
open scoped Topology
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters WeightedGlobalCoverScale
set_option maxRecDepth 10000
namespace ThreeSum.WeightedGlobalEntropyRates
theorem _root_.solution (m : ℕ) : Real.log (partitionCap m : ℝ)=
    (fixedLength m : ℝ)*Real.log 2*WeightedGlobalParameters.partitionEntropy := by
  unfold partitionCap
  rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_pow,Real.log_mul (by positivity) (by positivity),
    Real.log_pow,Real.log_pow]
  unfold WeightedGlobalParameters.partitionEntropy WeightedCacheParameters.Gn WeightedCacheParameters.pi1 WeightedCacheParameters.pi2 fixedPi fixedLength
  norm_num
  push_cast
  field_simp
  ring
end ThreeSum.WeightedGlobalEntropyRates
