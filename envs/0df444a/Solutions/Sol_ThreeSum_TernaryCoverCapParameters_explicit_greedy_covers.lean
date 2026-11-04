-- Prove2me | solution 1 for ThreeSum.TernaryCoverCapParameters.explicit_greedy_covers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:45:41.518384+00:00
-- url     : https://prove2.me/submissions/ea589dba-dde7-4f6b-80c9-f56c9c4be626

import Definitions.Def_Submission_ThreeSum_TernaryCoverFrequency
import Mathlib.Algebra.Order.Floor.Div
import Definitions.Def_Submission_ThreeSum_TernaryCoverCapParameters
import Theorems.Thm_ThreeSum_TernaryCoverCapParameters_rawThreshold_pos
import Theorems.Thm_ThreeSum_TernaryCoverCapParameters_actual_pruning_guard
import Theorems.Thm_ThreeSum_TernaryCoverCapParameters_sourceCap_threshold
import Theorems.Thm_ThreeSum_TernaryCoverCapParameters_frequencyFactor_gt_one
import Theorems.Thm_ThreeSum_TernaryCoverFrequency_greedy_covers
import Theorems.Thm_ThreeSum_TernaryCoverFrequency_polynomial_frequency_scale


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCoverCapParameters
open TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryCoverGoodMaps TernaryCoverFrequency TernaryPartitionCount TernaryTypeLowerBound
namespace ThreeSum.TernaryCoverCapParameters
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
end ThreeSum.TernaryCoverCapParameters
