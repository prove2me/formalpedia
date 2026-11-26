-- Prove2me | solution 1 for P2M_BKAR_Forest_exists_followOrder__eq_some_support_of_mem_edgeSetOrders_94b5d7b04ff1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:51:59.875003+00:00
-- url     : https://prove2.me/submissions/f1370317-cdf0-45b8-b8df-5b4b49a62ebc

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_FollowOrder
import Theorems.Thm_P2M_BKAR_Forest_exists_followOrder__eq_some_of_acyclic_union_cd131d32a109
import Theorems.Thm_BKAR_ForestIndex_ext
import Theorems.Thm_BKAR_Forest_OrderedGrowth_support_edges
import Theorems.Thm_BKAR_Forest_TerminalGrowth_support_edges
import Theorems.Thm_BKAR_Forest_empty_edges
import Theorems.Thm_BKAR_Forest_nodup_of_mem_edgeSetOrders
import Theorems.Thm_BKAR_Forest_support_edges
import Theorems.Thm_BKAR_Forest_toFinset_eq_of_mem_edgeSetOrders


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    {I : ForestIndex V} {order : List (Edge V)}
    (horder : order ∈ edgeSetOrders I.edges) :
    ∃ G : Forest V,
      followOrder? choices (Forest.empty V) order = some G ∧
        G.support = I := by
  have hset : order.toFinset = I.edges :=
    toFinset_eq_of_mem_edgeSetOrders horder
  have hnodup : order.Nodup :=
    nodup_of_mem_edgeSetOrders horder
  have hunion :
      order.toFinset ∪ (Forest.empty V).edges = I.edges := by
    rw [Forest.empty_edges, Finset.union_empty, hset]
  have hdisj : Disjoint order.toFinset (Forest.empty V).edges := by
    rw [Forest.empty_edges]
    exact Finset.disjoint_empty_right order.toFinset
  rcases exists_followOrder?_eq_some_of_acyclic_union choices order
      I.acyclic hunion hnodup hdisj with
    ⟨G, hfollow, hGedges⟩
  refine ⟨G, hfollow, ?_⟩
  apply ForestIndex.ext
  rw [Forest.support_edges, hGedges]
end BKAR.Forest
