-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.all_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:37:42.958245+00:00
-- url     : https://prove2.me/submissions/7ed0710a-eb8d-4560-a176-d71582fd4b12

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_reachable_mem_of_adj_closed
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_exists_positive
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_not_zero_adj_positive

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
    (hdelete : DeletionCenters G) (hr : 1 ≤ G.radius.toNat)
    (hcut : ∃ x, ¬ (G.induce ({x}ᶜ : Set α)).Connected) :
    ∀ c, 0 < (F.path c).length := by
  obtain ⟨a, ha⟩ := F.exists_positive hG hcard hK hdel hcut
  have hclosed : ∀ u ∈ {c : ↥(K : Set α) | 0 < (F.path c).length},
      ∀ v, (G.induce (K : Set α)).Adj u v → 0 < (F.path v).length := by
    intro u hu v huv
    by_contra hv
    have hvzero : (F.path v).length = 0 := by omega
    exact F.not_zero_adj_positive hG hcard hK hdel hdelete hr v u huv.symm hvzero hu
  intro c
  exact reachable_mem_of_adj_closed hclosed (hK a c) ha
end WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
