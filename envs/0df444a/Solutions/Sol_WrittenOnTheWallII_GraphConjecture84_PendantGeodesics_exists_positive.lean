-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.exists_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:35:05.216872+00:00
-- url     : https://prove2.me/submissions/837a6c7c-7a0f-4e2b-9e1e-43f177e9ba0e

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_dist_add_dist_eq_of_mem_geodesic
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_core_reachable_compl
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_exists_core_vertex_ne_two

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
open WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
variable {G : SimpleGraph α} {K : Finset α} (F : PendantGeodesics G K)
namespace WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
theorem _root_.solution (hG : G.Connected) (hcard : 3 ≤ K.card)
    (hK : (G.induce (K : Set α)).Connected)
    (hdel : ∀ x : ↥(K : Set α),
      ((G.induce (K : Set α)).induce ({x}ᶜ : Set ↥(K : Set α))).Connected)
    (hcut : ∃ x, ¬ (G.induce ({x}ᶜ : Set α)).Connected) :
    ∃ c, 0 < (F.path c).length := by
  by_contra! hn
  have hall : ∀ z : α, z ∈ K := by
    intro z
    obtain ⟨c, hzc⟩ := F.cover z
    have hsum := dist_add_dist_eq_of_mem_geodesic (F.path c) (F.geodesic c) hzc
    have hlen : (F.path c).length = 0 := by have := hn c; omega
    rw [← F.geodesic c, hlen] at hsum
    have hcz : G.dist (c : α) z = 0 := by omega
    exact (hG.dist_eq_zero_iff.mp hcz) ▸ c.property
  obtain ⟨x, hx⟩ := hcut
  obtain ⟨u, hux, _⟩ := exists_core_vertex_ne_two hcard x x
  apply hx
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨u, by simpa using hux⟩, ?_⟩
  intro z
  exact core_reachable_compl K hK hdel x u.property (hall z) hux z.property
end WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
