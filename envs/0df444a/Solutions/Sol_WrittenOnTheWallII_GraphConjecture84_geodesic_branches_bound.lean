-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.geodesic_branches_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:32:23.983478+00:00
-- url     : https://prove2.me/submissions/a16a9686-6f3f-4bd2-a7d3-40f72416ea41

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_induce_union_geodesic_isTree
public import Theorems.Thm_SimpleGraph_Walk_induce_support_isTree_of_length_eq_dist
public import Theorems.Thm_SimpleGraph_card_le_largestInducedTreeSize


set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α} (hG : G.Connected)
    {c a b : α} (p : G.Walk c a) (q : G.Walk c b)
    (hp : p.length = G.dist c a) (hq : q.length = G.dist c b)
    (hinter : ∀ z ∈ p.support, z ∈ q.support → z = c)
    (hsep : ∀ z ∈ p.support, z ≠ c → ∀ y ∈ q.support, y ≠ c → ¬ G.Adj z y) :
    p.length + q.length + 1 ≤ largestInducedTreeSize G := by
  classical
  have hprev : p.reverse.length = G.dist a c := by
    simpa only [Walk.length_reverse, SimpleGraph.dist_comm] using hp
  have hT := induce_union_geodesic_isTree hG p.reverse hprev q.support.toFinset
    (q.induce_support_isTree_of_length_eq_dist hq) (by simp) (by
      intro z hz hzs
      exact hinter z (by simpa only [Walk.support_reverse, List.mem_reverse] using hz)
        (by simpa only [List.mem_toFinset] using hzs)) (by
      intro z hz hzc y hy hzy
      by_contra hyc
      exact hsep z (by simpa only [Walk.support_reverse, List.mem_reverse] using hz) hzc y
        (by simpa only [List.mem_toFinset] using hy) hyc hzy)
  have hset : p.reverse.support.toFinset ∪ q.support.toFinset =
      p.support.toFinset ∪ q.support.toFinset := by ext z; simp
  rw [hset] at hT
  have hcardp : p.support.toFinset.card = p.length + 1 := by
    rw [List.toFinset_card_of_nodup (p.isPath_of_length_eq_dist hp).support_nodup,
      p.length_support]
  have hcardq : q.support.toFinset.card = q.length + 1 := by
    rw [List.toFinset_card_of_nodup (q.isPath_of_length_eq_dist hq).support_nodup,
      q.length_support]
  have hinterset : p.support.toFinset ∩ q.support.toFinset = {c} := by
    ext z
    simp only [Finset.mem_inter, List.mem_toFinset, Finset.mem_singleton]
    constructor
    · exact fun ⟨hzp, hzq⟩ => hinter z hzp hzq
    · intro hzc
      subst z
      exact ⟨p.start_mem_support, q.start_mem_support⟩
  have hbound := card_le_largestInducedTreeSize hT
  rw [Finset.card_union, hcardp, hcardq, hinterset, Finset.card_singleton] at hbound
  omega
end WrittenOnTheWallII.GraphConjecture84
