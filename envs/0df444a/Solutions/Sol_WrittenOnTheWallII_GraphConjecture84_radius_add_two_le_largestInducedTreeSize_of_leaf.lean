-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.radius_add_two_le_largestInducedTreeSize_of_leaf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:32:20.17756+00:00
-- url     : https://prove2.me/submissions/33b3707f-6c3f-4360-b823-e83a064099ed

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_dist_add_dist_eq_of_mem_geodesic
public import Theorems.Thm_SimpleGraph_IsTree_induce_insert_of_unique_adj
public import Theorems.Thm_SimpleGraph_Walk_induce_support_isTree_of_length_eq_dist
public import Theorems.Thm_SimpleGraph_card_le_largestInducedTreeSize


set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α}
    [DecidableRel G.Adj] (hG : G.Connected) {u : α} (hu : G.degree u = 1)
    (hr : 2 ≤ G.radius.toNat) : G.radius.toNat + 2 ≤ largestInducedTreeSize G := by
  classical
  haveI : Nonempty α := ⟨u⟩
  obtain ⟨v, huv, huniq⟩ := degree_eq_one_iff_existsUnique_adj.mp hu
  obtain ⟨w, hw⟩ := G.exists_edist_eq_eccent_of_finite v
  have hrw : G.radius.toNat ≤ G.dist v w :=
    ENat.toNat_le_toNat (hw ▸ G.radius_le_eccent)
      (edist_ne_top_iff_reachable.mpr (hG v w))
  have hwu : w ≠ u := by
    intro heq
    have hdist : G.dist v w = 1 := by
      rw [heq]
      exact dist_eq_one_iff_adj.mpr huv.symm
    omega
  have huw : G.dist u w = G.dist v w + 1 := by
    obtain ⟨q, hq⟩ := hG.exists_walk_length_eq_dist u w
    cases q with
    | nil => exact (hwu rfl).elim
    | @cons u b w hub q =>
      have hbv := huniq b hub
      subst b
      have htail := length_eq_dist_of_subwalk hq (Walk.isSubwalk_cons q hub)
      simpa only [Walk.length_cons, htail] using hq.symm
  obtain ⟨p, hp, hplen⟩ := hG.exists_path_of_dist v w
  have hunot : u ∉ p.support.toFinset := by
    intro humem
    have humem' : u ∈ p.support := by simpa using humem
    have hsum := dist_add_dist_eq_of_mem_geodesic p hplen humem'
    have hvu : G.dist v u = 1 := dist_eq_one_iff_adj.mpr huv.symm
    omega
  have hT := p.induce_support_isTree_of_length_eq_dist hplen
  have hi := hT.induce_insert_of_unique_adj hunot (by simp) huv
    (by intro b _ hub; exact huniq b hub)
  have hle := card_le_largestInducedTreeSize hi
  have hcard : (insert u p.support.toFinset).card = p.length + 2 := by
    rw [Finset.card_insert_of_notMem hunot,
      List.toFinset_card_of_nodup hp.support_nodup, p.length_support]
  rw [hcard, hplen] at hle
  omega
end WrittenOnTheWallII.GraphConjecture84
