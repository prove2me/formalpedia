-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.radius_le_core_radius_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:35:21.542802+00:00
-- url     : https://prove2.me/submissions/d958d119-7376-4740-b2fb-51075c8038ac

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_dist_add_dist_eq_of_mem_geodesic
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_dist_from_core

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
open WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
variable {G : SimpleGraph α} {K : Finset α} (F : PendantGeodesics G K)
namespace WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
theorem _root_.solution (hG : G.Connected)
    (hK : (G.induce (K : Set α)).Connected) (L : ℕ)
    (hLen : ∀ c, (F.path c).length = L) :
    G.radius.toNat ≤ (G.induce (K : Set α)).radius.toNat + L := by
  classical
  haveI : Nonempty α := hG.nonempty
  haveI : Nonempty ↥(K : Set α) := hK.nonempty
  let H := G.induce (K : Set α)
  obtain ⟨v, hv⟩ := H.exists_eccent_eq_radius
  obtain ⟨z, hz⟩ := G.exists_edist_eq_eccent_of_finite (v : α)
  obtain ⟨c, hzc⟩ := F.cover z
  have hdist := F.dist_from_core hG c v hzc
  have hsum := dist_add_dist_eq_of_mem_geodesic (F.path c) (F.geodesic c) hzc
  rw [← F.geodesic c, hLen c] at hsum
  obtain ⟨p, hp⟩ := hK.exists_walk_length_eq_dist v c
  have hmap := G.dist_le (p.map (SimpleGraph.Embedding.induce (K : Set α)).toHom)
  rw [Walk.length_map, hp] at hmap
  change G.dist (v : α) c ≤ H.dist v c at hmap
  have hvc : H.dist v c ≤ H.radius.toNat :=
    ENat.toNat_le_toNat (hv ▸ H.edist_le_eccent) (H.radius_ne_top_iff.mpr hK)
  have hrad : G.radius.toNat ≤ G.dist (v : α) z :=
    ENat.toNat_le_toNat (hz ▸ G.radius_le_eccent)
      (edist_ne_top_iff_reachable.mpr (hG v z))
  dsimp only [H] at hmap hvc
  omega
end WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
