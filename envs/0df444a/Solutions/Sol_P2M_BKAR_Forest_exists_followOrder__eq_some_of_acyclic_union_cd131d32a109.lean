-- Prove2me | solution 1 for P2M_BKAR_Forest_exists_followOrder__eq_some_of_acyclic_union_cd131d32a109
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:49:51.755251+00:00
-- url     : https://prove2.me/submissions/82813783-3a1c-4568-9566-0e89a87648f9

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_FollowOrder
import Theorems.Thm_BKAR_EdgePath_IsPath_mono
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_mono
import Theorems.Thm_BKAR_ForestIndex_ext
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_derivativeOrder_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_cons
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_nil
import Theorems.Thm_BKAR_Forest_acyclic_insert_iff_edge
import Theorems.Thm_BKAR_Forest_emptyActiveEdge_val
import Theorems.Thm_BKAR_Forest_mem_activeEdges_of_not_inSameComponent
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_pathMin_nil
import Theorems.Thm_BKAR_IsAcyclicEdgeSet_mono
import Theorems.Thm_BKAR_OrderedSimplexParams_tail
import Theorems.Thm_BKAR_edgeBasis_self
import Theorems.Thm_BKAR_mixedPartialList_cons
import Theorems.Thm_BKAR_mixedPartialList_cons_apply
import Theorems.Thm_BKAR_mixedPartialList_nil
import Theorems.Thm_BKAR_mixedPartialList_nil_apply
import Theorems.Thm_BKAR_orderedSimplexIntegralAux_cons
import Theorems.Thm_BKAR_orderedSimplexIntegralAux_nil
import Theorems.Thm_BKAR_orderedSimplexIntegral_cons
import Theorems.Thm_BKAR_orderedSimplexIntegral_nil
import Theorems.Thm_BKAR_orderedSimplexParams_cons
import Theorems.Thm_BKAR_orderedSimplexParams_nil
import Theorems.Thm_BKAR_updateCoord_same_value
import Theorems.Thm_BKAR_updateCoord_self
import Theorems.Thm_BKAR_updateCoord_update_same
attribute [local simp] BKAR.Forest.OrderedGrowth.branchIntegralAux_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.branchIntegral_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.branchIntegrand_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.derivativeOrder_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.params_cons_cons
attribute [local simp] BKAR.Forest.OrderedGrowth.params_cons_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.params_nil
attribute [local simp] BKAR.Forest.emptyActiveEdge_val
attribute [local simp] BKAR.Forest.paramValue_of_mem
attribute [local simp] BKAR.Forest.pathMin_cons
attribute [local simp] BKAR.Forest.pathMin_nil
attribute [local simp] BKAR.edgeBasis_self
attribute [local simp] BKAR.mixedPartialList_cons
attribute [local simp] BKAR.mixedPartialList_cons_apply
attribute [local simp] BKAR.mixedPartialList_nil
attribute [local simp] BKAR.mixedPartialList_nil_apply
attribute [local simp] BKAR.orderedSimplexIntegralAux_cons
attribute [local simp] BKAR.orderedSimplexIntegralAux_nil
attribute [local simp] BKAR.orderedSimplexIntegral_cons
attribute [local simp] BKAR.orderedSimplexIntegral_nil
attribute [local simp] BKAR.orderedSimplexParams_cons
attribute [local simp] BKAR.orderedSimplexParams_nil
attribute [local simp] BKAR.updateCoord_same_value
attribute [local simp] BKAR.updateCoord_self
attribute [local simp] BKAR.updateCoord_update_same



set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V) :
    ∀ {F : Forest V} {S : Finset (Edge V)} (order : List (Edge V)),
      IsAcyclicEdgeSet S →
      order.toFinset ∪ F.edges = S →
      order.Nodup →
      Disjoint order.toFinset F.edges →
      ∃ G : Forest V, followOrder? choices F order = some G ∧
        G.edges = S
  | F, S, [], _hS, hset, _hnodup, _hdisj => by
      refine ⟨F, ?_, ?_⟩
      · rfl
      · rw [List.toFinset_nil, Finset.empty_union] at hset
        exact hset
  | F, S, e :: tail, hS, hset, hnodup, hdisj => by
      have hnotMemTail : e ∉ tail := by
        exact (List.nodup_cons.mp hnodup).1
      have htailNodup : tail.Nodup := by
        exact (List.nodup_cons.mp hnodup).2
      have hnotMemF : e ∉ F.edges := by
        rw [List.toFinset_cons, Finset.disjoint_insert_left] at hdisj
        exact hdisj.1
      have htailDisjF : Disjoint tail.toFinset F.edges := by
        rw [List.toFinset_cons, Finset.disjoint_insert_left] at hdisj
        exact hdisj.2
      have hinsertSub : insert e F.edges ⊆ S := by
        intro x hx
        rw [← hset]
        rw [List.toFinset_cons]
        rw [Finset.mem_union]
        rw [Finset.mem_insert] at hx
        exact hx.elim
          (fun hx => Or.inl (by
            rw [hx]
            exact Finset.mem_insert_self e tail.toFinset))
          (fun hx => Or.inr hx)
      have hacyclicInsert : IsAcyclicEdgeSet (insert e F.edges) :=
        IsAcyclicEdgeSet.mono hS hinsertSub
      have he : e ∈ F.activeEdges :=
        F.mem_activeEdges_of_not_inSameComponent
          ((F.acyclic_insert_iff_edge hnotMemF).mp hacyclicInsert)
      let F' : Forest V := (choices F ⟨e, he⟩).forest
      have hchildSet : tail.toFinset ∪ F'.edges = S := by
        rw [show F'.edges = insert e F.edges by
          exact (choices F ⟨e, he⟩).extension.edges_eq]
        ext x
        rw [← hset]
        simp [List.toFinset_cons, or_comm]
      have hchildDisj : Disjoint tail.toFinset F'.edges := by
        rw [show F'.edges = insert e F.edges by
          exact (choices F ⟨e, he⟩).extension.edges_eq]
        rw [Finset.disjoint_left]
        intro x hxTail hxInsert
        rw [Finset.mem_insert] at hxInsert
        cases hxInsert with
        | inl hxe =>
            exact hnotMemTail (hxe ▸ List.mem_toFinset.mp hxTail)
        | inr hxF =>
            rw [Finset.disjoint_left] at htailDisjF
            exact htailDisjF hxTail hxF
      rcases solution choices tail
          hS hchildSet htailNodup hchildDisj with
        ⟨G, hfollow, hGedges⟩
      refine ⟨G, ?_, hGedges⟩
      simp [followOrder?, he]
      exact hfollow
end BKAR.Forest
