-- Prove2me | solution 1 for ThreeSum.WeightedGlobalCoverCapParameters.explicit_greedy_covers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:47:34.298764+00:00
-- url     : https://prove2.me/submissions/7666873c-ee70-4b38-9ea7-b96d8847a5ed

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCoverFrequency
import Mathlib.Algebra.Order.Floor.Div
import Definitions.Def_Submission_Weighted_Global_TernaryCoverCapParameters
import Theorems.Thm_ThreeSum_WeightedGlobalCoverCapParameters_rawThreshold_pos
import Theorems.Thm_ThreeSum_WeightedGlobalCoverCapParameters_actual_pruning_guard
import Theorems.Thm_ThreeSum_WeightedGlobalCoverCapParameters_sourceCap_threshold
import Theorems.Thm_ThreeSum_WeightedGlobalCoverCapParameters_frequencyFactor_gt_one
import Theorems.Thm_ThreeSum_WeightedGlobalCoverFrequency_greedy_covers
import Theorems.Thm_ThreeSum_WeightedGlobalCoverFrequency_polynomial_frequency_scale


set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalCoverCapParameters
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open WeightedGlobalCoverGoodMaps WeightedGlobalCoverFrequency WeightedGlobalPartitionCount TernaryTypeLowerBound
namespace ThreeSum.WeightedGlobalCoverCapParameters
theorem _root_.solution (m p : ℕ) [Fact p.Prime]
    (maps : List (Weight m p)) (hall : ∀ w, w ∈ maps) (hp : 4 < p)
    (hlo : (vertices (fixedLength m) (fixedPi m)).card*
      (2^(fixedPi m 1)*3^(fixedPi m 2)) ≤ p^2)
    (hup : p^2 ≤ 16*(vertices (fixedLength m) (fixedPi m)).card*
      (2^(fixedPi m 1)*3^(fixedPi m 2)))
    (k : ℕ) (hk : 0 < k) (t : ZMod p × ZMod p) :
    ∃ w ∈ Cover.greedyChoices maps
        (Covers m p (sourceCap m p) (rawThreshold p (sourceCap m p) k)) Finset.univ
        (frequencyFactor m*(Nat.log2 (p^2)+1)),
      Covers m p (sourceCap m p) (rawThreshold p (sourceCap m p) k) w t := by
  apply greedy_covers m p maps hall hp hlo (sourceCap m p) k
    (rawThreshold p (sourceCap m p) k) (frequencyFactor m) (frequencyFactor_gt_one m)
    (rawThreshold_pos p (sourceCap m p) k) (sourceCap_threshold m p (by omega))
    (actual_pruning_guard m p (sourceCap m p) k hk) (polynomial_frequency_scale m p hup) t
end ThreeSum.WeightedGlobalCoverCapParameters
