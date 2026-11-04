-- Prove2me | solution 1 for ThreeSum.TernaryCoverOutputCap.edges_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:47:15.835066+00:00
-- url     : https://prove2.me/submissions/a85c59bb-8c27-4701-a951-bd9851f59911

import Definitions.Def_Submission_ThreeSum_TernaryCoverRegularity
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryCoverOutputCap
import Theorems.Thm_ThreeSum_TernaryCoverOutputCap_outputFiber_card_le
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_TernaryCoverLocal_edge_data
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_mapEdge_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_output_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_reindex_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_swapEdge_swapEdge
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.mapEdge_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.output_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.reindex_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.swapEdge_swapEdge



set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverOutputCap
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}
namespace ThreeSum.TernaryCoverOutputCap
theorem _root_.solution (α π : DigitType) :
    Fintype.card (LocalEdge L α π) ≤ (vertices L π).card * (2^(π 1)*3^(π 2)) := by
  classical
  have h := card_eq_sum_card_fiberwise (s := (univ : Finset (LocalEdge L α π)))
    (t := vertices L π) (f := output)
    (fun e _ => mem_filter.mpr ⟨mem_univ _, (edge_data e).2.2.1⟩)
  have hf (q : TritWord L) (hq : q ∈ vertices L π) :
      (univ.filter (fun e : LocalEdge L α π => output e = q)).card ≤ 2^(π 1)*3^(π 2) := by
    rw [← Fintype.card_subtype]
    exact outputFiber_card_le α π q ((mem_filter.mp hq).2)
  calc
    _ = ∑ q ∈ vertices L π, (univ.filter (fun e : LocalEdge L α π => output e = q)).card :=
      by simpa only [card_univ] using h
    _ ≤ ∑ _q ∈ vertices L π, (2^(π 1)*3^(π 2)) := sum_le_sum (fun q hq => hf q hq)
    _ = _ := by simp
end ThreeSum.TernaryCoverOutputCap
