-- Prove2me | solution 1 for ThreeSum.TernaryCoverRegularity.source_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:39:51.015551+00:00
-- url     : https://prove2.me/submissions/4e12b6b8-36ec-40cc-8b4b-d57b8bda09b8

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
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_sourceFiber_card_equal
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_TernaryCoverLocal_left_mem_vertices
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
theorem _root_.solution {α π : DigitType} {a : TritWord L} (ha : HasType a α) :
    Fintype.card (LocalEdge L α π) =
      (vertices L α).card * Fintype.card (sourceFiber α π a) := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (univ : Finset (LocalEdge L α π))) (t := vertices L α) (f := left)
    (fun e _ => left_mem_vertices e)
  have hf (b : TritWord L) (hb : b ∈ vertices L α) :
      (univ.filter (fun e : LocalEdge L α π => left e = b)).card =
        Fintype.card (sourceFiber α π a) := by
    rw [← Fintype.card_subtype]
    exact sourceFiber_card_equal ((mem_filter.mp hb).2) ha
  calc
    _ = ∑ b ∈ vertices L α, (univ.filter (fun e : LocalEdge L α π => left e = b)).card :=
      by simpa only [card_univ] using h
    _ = ∑ _b ∈ vertices L α, Fintype.card (sourceFiber α π a) :=
      sum_congr rfl (fun b hb => hf b hb)
    _ = _ := by simp
end ThreeSum.TernaryCoverRegularity
