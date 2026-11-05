-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSchedule.same_type_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:10:42.34003+00:00
-- url     : https://prove2.me/submissions/129b6773-3822-4da1-8b64-a1dab4ad6f09

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryEuler
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Schedule
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedSchedule_cacheCost_counts

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSchedule
open TernaryJointType WeightedBankEnumeration
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSchedule
theorem _root_.solution {N : ℕ} {Q R : TritWord N} {π : DigitType}
    (hQ : HasType Q π) (hR : HasType R π) : cacheCost Q=cacheCost R := by
  rw [cacheCost_counts,cacheCost_counts,hQ 1,hQ 2,hR 1,hR 2]
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedSchedule
