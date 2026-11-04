-- Prove2me | solution 1 for ThreeSum.TernaryCoverRegularity.source_degree_le_vertices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:34:57.821364+00:00
-- url     : https://prove2.me/submissions/b3421b65-5fe5-46c5-867b-f862fafc934f

import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_output_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_reindex_symm
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_mapEdge_symm
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_TernaryCoverLocal_endpoint_injective
import Theorems.Thm_ThreeSum_TernaryCoverLocal_right_mem_vertices
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
theorem _root_.solution (α π : DigitType) (a : TritWord L) :
    Fintype.card (sourceFiber α π a) ≤ (vertices L α).card := by
  classical
  let f : sourceFiber α π a → {b // b ∈ vertices L α} :=
    fun e => ⟨right e.val, right_mem_vertices e.val⟩
  have hf : Function.Injective f := by
    intro e e' h
    apply Subtype.ext
    apply endpoint_injective α π
    exact Prod.ext (e.property.trans e'.property.symm) (congrArg Subtype.val h)
  simpa using Fintype.card_le_of_injective f hf
end ThreeSum.TernaryCoverRegularity
