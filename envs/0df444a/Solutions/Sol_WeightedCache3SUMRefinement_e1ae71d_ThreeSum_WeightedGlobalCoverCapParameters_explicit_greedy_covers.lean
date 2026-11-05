-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverCapParameters.explicit_greedy_covers
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:37:22.185116+00:00
-- url     : https://prove2.me/submissions/56e0eed5-e6d7-43ef-859f-1de64a23e8fb

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverFrequency
import Mathlib.Algebra.Order.Floor.Div
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCoverCapParameters
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCoverCapParameters_rawThreshold_pos
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCoverCapParameters_actual_pruning_guard
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCoverCapParameters_sourceCap_threshold
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCoverCapParameters_frequencyFactor_gt_one
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCoverFrequency_greedy_covers
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCoverFrequency_polynomial_frequency_scale


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverCapParameters
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open WeightedGlobalCoverGoodMaps WeightedGlobalCoverFrequency WeightedGlobalPartitionCount TernaryTypeLowerBound
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverCapParameters
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
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalCoverCapParameters
