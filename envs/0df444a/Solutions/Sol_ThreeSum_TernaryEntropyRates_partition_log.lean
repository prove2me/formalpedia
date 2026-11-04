-- Prove2me | solution 1 for ThreeSum.TernaryEntropyRates.partition_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:59:43.033988+00:00
-- url     : https://prove2.me/submissions/5129f3c6-cf6a-4ac9-bc9e-3545f348b641

import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Definitions.Def_Submission_ThreeSum_TernaryEntropyRates

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryEntropyRates
open Filter Real
open scoped Topology
open TernaryJointType TernaryCoverLocal TernaryLocalParameters TernaryCoverScale
set_option maxRecDepth 10000
namespace ThreeSum.TernaryEntropyRates
theorem _root_.solution (m : ℕ) : Real.log (partitionCap m : ℝ)=
    (fixedLength m : ℝ)*Real.log 2*TernaryParameters.partitionEntropy := by
  unfold partitionCap
  rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_pow,Real.log_mul (by positivity) (by positivity),
    Real.log_pow,Real.log_pow]
  unfold TernaryParameters.partitionEntropy TernaryParameters.pi1 TernaryParameters.pi2
    TernaryParameters.three fixedPi fixedLength
  norm_num
  push_cast
  field_simp
  ring
end ThreeSum.TernaryEntropyRates
