-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.radius_le_radius_induce_of_dominated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:32:41.983721+00:00
-- url     : https://prove2.me/submissions/badcba6f-f015-4d7f-a533-e715d9270584

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α} (hG : G.Connected)
    (S : Set α) [DecidablePred (· ∈ S)] (hS : (G.induce S).Connected)
    (hdom : ∀ v ∈ S, ∀ z ∉ S, ∃ w ∈ S, G.dist v z ≤ G.dist v w) :
    G.radius.toNat ≤ (G.induce S).radius.toNat := by
  haveI : Nonempty S := hS.nonempty
  let H := G.induce S
  obtain ⟨v, hv⟩ := H.exists_eccent_eq_radius
  have hfin : H.radius ≠ ⊤ := H.radius_ne_top_iff.mpr hS
  have hdist (w : S) : G.dist v w ≤ H.radius.toNat := by
    obtain ⟨p, hp⟩ := hS.exists_walk_length_eq_dist v w
    have hmap := G.dist_le (p.map (SimpleGraph.Embedding.induce S).toHom)
    rw [Walk.length_map] at hmap
    change G.dist (v : α) (w : α) ≤ p.length at hmap
    have hcenter : H.dist v w ≤ H.radius.toNat :=
      ENat.toNat_le_toNat (hv ▸ (H.edist_le_eccent (u := v) (v := w))) hfin
    exact hmap.trans (hp ▸ hcenter)
  obtain ⟨z, hz⟩ := G.exists_edist_eq_eccent_of_finite (v : α)
  have hrz : G.radius.toNat ≤ G.dist v z :=
    ENat.toNat_le_toNat (hz ▸ G.radius_le_eccent)
      (edist_ne_top_iff_reachable.mpr (hG v z))
  by_cases hzs : z ∈ S
  · exact hrz.trans (hdist ⟨z, hzs⟩)
  · obtain ⟨w, hw, hzw⟩ := hdom v v.property z hzs
    exact hrz.trans (hzw.trans (hdist ⟨w, hw⟩))
end WrittenOnTheWallII.GraphConjecture84
