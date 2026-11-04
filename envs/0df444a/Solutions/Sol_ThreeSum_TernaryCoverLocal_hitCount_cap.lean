-- Prove2me | solution 1 for ThreeSum.TernaryCoverLocal.hitCount_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:06:42.852011+00:00
-- url     : https://prove2.me/submissions/46db6887-882e-4746-99a6-e892ba364282

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Definitions.Def_Submission_ThreeSum_TernaryCoverTrimming
import Definitions.Def_Submission_ThreeSum_TernaryCoverFibers
import Definitions.Def_Submission_ThreeSum_TernaryCoverRetained
import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Theorems.Thm_ThreeSum_TernaryCoverLocal_fieldLeft_mem
import Theorems.Thm_ThreeSum_TernaryCoverLocal_fieldRight_mem
import Theorems.Thm_ThreeSum_TernaryCoverLocal_field_endpoint_injective
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_TernaryCoverRetained_hits_card_le_sq
attribute [local simp] ThreeSum.HashFamily.hashMap_apply



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverLocal
open Finset TernaryJointType TernaryCoverHashes
open scoped BigOperators
variable {L p : ℕ}
variable [Fact (Nat.Prime p)]
namespace ThreeSum.TernaryCoverLocal
theorem _root_.solution (α π : DigitType) (B : ℕ)
    (w : Coordinate (Fin L) → ZMod p) (a b : ZMod p) (hp : 2 < p) :
    hitCount α π B w a b ≤ B ^ 2 := by
  classical
  let F : Finset (LocalEdge L α π) := univ.filter fun e => w ∈ trimmedEvents α π B a b e
  change F.card ≤ B ^ 2
  by_cases hz : F.card = 0
  · simp [hz]
  obtain ⟨e, he⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hz)
  have hlights :
      TernaryCoverTrimming.bucketSize (fieldVertices L p α) leftVector w a ≤ B ∧
      TernaryCoverTrimming.bucketSize (fieldVertices L p α) rightVector w b ≤ B :=
    (mem_filter.mp (mem_filter.mp he).2).2
  have hsub : F ⊆ TernaryCoverRetained.hits (fieldLeft (p := p)) (fieldRight (p := p))
      (fun x => linearHash (leftVector x) w) (fun y => linearHash (rightVector y) w) a b := by
    intro f hf
    have ht := (mem_filter.mp hf).2
    have hh := (mem_filter.mp (mem_filter.mp ht).1).2
    exact mem_filter.mpr ⟨mem_univ _, hh⟩
  exact (card_le_card hsub).trans
    (TernaryCoverRetained.hits_card_le_sq (fieldLeft (p := p)) (fieldRight (p := p))
      (fun x => linearHash (leftVector x) w) (fun y => linearHash (rightVector y) w)
      (fieldVertices L p α) (fieldVertices L p α) (field_endpoint_injective α π hp)
      fieldLeft_mem fieldRight_mem a b B hlights.1 hlights.2)
end ThreeSum.TernaryCoverLocal
