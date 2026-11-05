-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalEntropyRates.partition_log
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:25:49.958535+00:00
-- url     : https://prove2.me/submissions/e0a5a6a1-f15d-448d-b988-e24e0f59879a

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalParameters
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverScale
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryEntropyRates

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalEntropyRates
open Filter Real
open scoped Topology
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters WeightedGlobalCoverScale
set_option maxRecDepth 10000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalEntropyRates
theorem _root_.solution (m : ℕ) : Real.log (partitionCap m : ℝ)=
    (fixedLength m : ℝ)*Real.log 2*WeightedGlobalParameters.partitionEntropy := by
  unfold partitionCap
  rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_pow,Real.log_mul (by positivity) (by positivity),
    Real.log_pow,Real.log_pow]
  unfold WeightedGlobalParameters.partitionEntropy WeightedCacheParameters_e1ae71d.Gn WeightedCacheParameters_e1ae71d.pi1 WeightedCacheParameters_e1ae71d.pi2 fixedPi fixedLength
  norm_num
  push_cast
  field_simp
  ring
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalEntropyRates
