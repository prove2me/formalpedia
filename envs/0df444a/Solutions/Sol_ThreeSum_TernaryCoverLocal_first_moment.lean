-- Prove2me | solution 1 for ThreeSum.TernaryCoverLocal.first_moment
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:32:57.881466+00:00
-- url     : https://prove2.me/submissions/558e327c-c00b-4079-b7ff-d01538345118

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Definitions.Def_Submission_ThreeSum_TernaryCoverTrimming
import Definitions.Def_Submission_ThreeSum_TernaryCoverFibers
import Definitions.Def_Submission_ThreeSum_TernaryCoverRetained
import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_HashFamily_sum_incidenceCount
import Definitions.Def_WeightedCache3SUM_Alias_9cba9841773c016e
import Theorems.Thm_ThreeSum_TernaryCoverTrimming_trimmedPairEvent_bound
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverLocal
open Finset TernaryJointType TernaryCoverHashes
open scoped BigOperators
variable {L p : ℕ}
variable [Fact (Nat.Prime p)]
namespace ThreeSum.TernaryCoverLocal
theorem _root_.solution (α π : DigitType) (B : ℕ) (a b : ZMod p)
    (hB : 8 * (p + (fieldVertices L p α).card) ≤ B * p) :
    3 * Fintype.card (LocalEdge L α π) * Fintype.card (Coordinate (Fin L) → ZMod p) ≤
      4 * p ^ 2 * (∑ w : Coordinate (Fin L) → ZMod p, hitCount α π B w a b) := by
  unfold hitCount
  rw [HashFamily.sum_incidenceCount, mul_sum]
  calc
    _ = ∑ _e : LocalEdge L α π,
        3 * Fintype.card (Coordinate (Fin L) → ZMod p) := by simp; ring
    _ ≤ _ := by
      apply sum_le_sum
      intro e _
      have h := TernaryCoverTrimming.trimmedPairEvent_bound
        (fieldLeft (p := p) e) (fieldRight (p := p) e) a b
        (fieldVertices L p α) (fieldVertices L p α) B
        (by simpa using hB) (by simpa using hB)
      simpa [trimmedEvents] using h
end ThreeSum.TernaryCoverLocal
