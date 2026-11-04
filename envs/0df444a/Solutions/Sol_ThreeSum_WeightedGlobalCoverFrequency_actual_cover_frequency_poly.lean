-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCoverFrequency.actual_cover_frequency_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:44:09.347919+00:00
-- url     : https://prove2.me/submissions/4d7fa61e-6363-4ca2-a883-a113f0f2c958

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverGoodMaps
import Definitions.Def_Submission_ThreeSum_Greedy
import Definitions.Def_Submission_Weighted_Global_TernaryPartitionCount
import Definitions.Def_Submission_Weighted_Global_TernaryCoverFrequency
import Theorems.Thm_ThreeSum_WeightedGlobalCoverFrequency_actual_cover_frequency
import Theorems.Thm_ThreeSum_WeightedGlobalCoverFrequency_polynomial_frequency_scale

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalCoverFrequency
open Finset TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open WeightedGlobalCoverGoodMaps
open scoped BigOperators
variable (m p : ℕ) [Fact p.Prime]
namespace ThreeSum.WeightedGlobalCoverFrequency
theorem _root_.solution (hp : 4 < p)
    (hlo : (vertices (fixedLength m) (fixedPi m)).card*
      (2^(fixedPi m 1)*3^(fixedPi m 2)) ≤ p^2)
    (hup : p^2 ≤ 16*(vertices (fixedLength m) (fixedPi m)).card*
      (2^(fixedPi m 1)*3^(fixedPi m 2)))
    (B k τ : ℕ) (hτ : 0 < τ)
    (hB : 8*(p+(fieldVertices (fixedLength m) p (fixedAlpha m)).card) ≤ B*p)
    (hguard : 16*p^4*B^2*3^(4*k^2) ≤ τ^k*Fintype.card (ActualEdge m))
    (t : ZMod p × ZMod p) :
    Fintype.card (Weight m p) ≤ frequencyFactor m*
      (univ.filter fun w => Covers m p B τ w t).card :=
  actual_cover_frequency m p hp hlo B k τ (frequencyFactor m) hτ hB hguard
    (polynomial_frequency_scale m p hup) t
end ThreeSum.WeightedGlobalCoverFrequency
