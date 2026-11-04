-- Prove2me | solution 1 for ThreeSum.TernaryCoverRegularity.sourceFiber_card_equal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:34:56.712819+00:00
-- url     : https://prove2.me/submissions/f215f10c-668c-4b7d-b413-36ed962ea907

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_same_type_perm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_output_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_reindex_symm
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_mapEdge_symm
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
attribute [local simp] ThreeSum.HashFamily.hashMap_apply


attribute [local simp] ThreeSum.TernaryCoverRegularity.left_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.output_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.reindex_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.reindex_symm'
attribute [local simp] ThreeSum.TernaryCoverRegularity.mapEdge_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.mapEdge_symm'

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverRegularity
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}
namespace ThreeSum.TernaryCoverRegularity
theorem _root_.solution {α π : DigitType} {a b : TritWord L}
    (ha : HasType a α) (hb : HasType b α) :
    Fintype.card (sourceFiber α π a) = Fintype.card (sourceFiber α π b) := by
  classical
  obtain ⟨σ, hσ⟩ := same_type_perm ha hb
  have hinv : reindex σ.symm b = a := by rw [← hσ, reindex_symm]
  let e : sourceFiber α π a ≃ sourceFiber α π b :=
    { toFun := fun x => ⟨mapEdge σ x.val, by rw [left_mapEdge, x.property, hσ]⟩
      invFun := fun x => ⟨mapEdge σ.symm x.val, by rw [left_mapEdge, x.property, hinv]⟩
      left_inv := fun x => by apply Subtype.ext; exact mapEdge_symm σ _
      right_inv := fun x => by apply Subtype.ext; exact mapEdge_symm' σ _ }
  exact Fintype.card_congr e
end ThreeSum.TernaryCoverRegularity
