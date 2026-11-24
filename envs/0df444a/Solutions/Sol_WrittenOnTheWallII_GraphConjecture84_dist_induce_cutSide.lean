-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.dist_induce_cutSide
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:36:54.978397+00:00
-- url     : https://prove2.me/submissions/65d68b52-aa21-430c-b9a1-a59b253806f7

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_dist_add_dist_eq_of_mem_geodesic
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_geodesic_support_subset_cutSide
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_connected_induce_cutSide
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_length_induce_walk

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α} (hG : G.Connected)
    (c : α) (a : ↥({c}ᶜ : Set α)) (u v : cutSide G c a) :
    (G.induce (cutSide G c a)).dist u v = G.dist u v := by
  classical
  let S := cutSide G c a
  have hS := connected_induce_cutSide hG c a
  apply le_antisymm
  · obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist (u : α) v
    by_cases hc : c ∈ p.support
    · let pu := (p.takeUntil c hc).reverse
      let pv := p.dropUntil c hc
      have hpu : pu.length = G.dist c u := by
        simpa only [pu, Walk.length_reverse, SimpleGraph.dist_comm] using
          length_eq_dist_of_subwalk hp (p.isSubwalk_takeUntil hc)
      have hpv : pv.length = G.dist c v :=
        length_eq_dist_of_subwalk hp (p.isSubwalk_dropUntil hc)
      have hsu := geodesic_support_subset_cutSide hG a u.property pu hpu
      have hsv := geodesic_support_subset_cutSide hG a v.property pv hpv
      let q := (pu.induce S hsu).reverse.append (pv.induce S hsv)
      have hdist := (G.induce S).dist_le q
      have hlen : q.length = G.dist (u : α) v := by
        have hsum := dist_add_dist_eq_of_mem_geodesic p hp hc
        simp only [q, Walk.length_append, Walk.length_reverse, length_induce_walk, hpu, hpv]
        rw [G.dist_comm (u := c) (v := (u : α))]
        exact hsum
      exact hdist.trans_eq hlen
    · have hsub : ∀ z ∈ p.support, z ∈ ({c}ᶜ : Set α) := by
        intro z hz
        have hzc : z ≠ c := by intro heq; exact hc (heq ▸ hz)
        simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hzc
      have hu : (u : α) ≠ c := by
        intro huc
        exact hc (Eq.subst (motive := fun z : α => z ∈ p.support) huc p.start_mem_support)
      have hur : (G.induce ({c}ᶜ : Set α)).Reachable a
          ⟨(u : α), by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hu⟩ := by
        rcases u.property with huc | ⟨_, hu'⟩
        · exact (hu huc).elim
        · exact hu'
      have hsubS : ∀ z ∈ p.support, z ∈ S := by
        intro z hz
        have hzc : z ≠ c := by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hsub z hz
        refine Or.inr ⟨hzc, hur.trans ?_⟩
        exact ⟨(p.takeUntil z hz).induce ({c}ᶜ : Set α)
          (fun w hw => hsub w (p.support_takeUntil_subset hz hw))⟩
      have hdist := (G.induce S).dist_le (p.induce S hsubS)
      simpa only [length_induce_walk, hp] using hdist
  · obtain ⟨p, hp⟩ := hS.exists_walk_length_eq_dist u v
    have hdist := G.dist_le (p.map (SimpleGraph.Embedding.induce S).toHom)
    rw [Walk.length_map] at hdist
    change G.dist (u : α) (v : α) ≤ p.length at hdist
    exact hdist.trans_eq hp
end WrittenOnTheWallII.GraphConjecture84
