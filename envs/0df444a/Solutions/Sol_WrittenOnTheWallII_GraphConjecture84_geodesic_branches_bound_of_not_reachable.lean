-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.geodesic_branches_bound_of_not_reachable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:33:46.628782+00:00
-- url     : https://prove2.me/submissions/0f8833d0-66ec-4016-aae4-a99bf5dc8f2f

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_geodesic_branches_bound
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_reachable_compl_of_mem_geodesic

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α} (hG : G.Connected)
    {c a b : α} (ha : a ≠ c) (hb : b ≠ c)
    (hsep : ¬ (G.induce ({c}ᶜ : Set α)).Reachable
      ⟨a, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using ha⟩
      ⟨b, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hb⟩) :
    G.dist c a + G.dist c b + 1 ≤ largestInducedTreeSize G := by
  obtain ⟨p, _, hp⟩ := hG.exists_path_of_dist c a
  obtain ⟨q, _, hq⟩ := hG.exists_path_of_dist c b
  rw [← hp, ← hq]
  apply geodesic_branches_bound hG p q hp hq
  · intro z hzp hzq
    by_contra hzc
    have hza := reachable_compl_of_mem_geodesic p hp ha hzp hzc
    have hzb := reachable_compl_of_mem_geodesic q hq hb hzq hzc
    exact hsep (hza.symm.trans hzb)
  · intro z hzp hzc y hyq hyc hzy
    have hza := reachable_compl_of_mem_geodesic p hp ha hzp hzc
    have hyb := reachable_compl_of_mem_geodesic q hq hb hyq hyc
    have hadj : (G.induce ({c}ᶜ : Set α)).Adj
        ⟨z, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hzc⟩
        ⟨y, by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hyc⟩ := hzy
    exact hsep (hza.symm.trans (hadj.reachable.trans hyb))
end WrittenOnTheWallII.GraphConjecture84
