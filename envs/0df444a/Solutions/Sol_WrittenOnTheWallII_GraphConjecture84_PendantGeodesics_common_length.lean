-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.common_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:38:52.520313+00:00
-- url     : https://prove2.me/submissions/4888b7c4-acd5-491e-80e0-fb7a04c184f0

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_reachable_mem_of_adj_closed
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_length_le_of_adj

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
    (hdelete : DeletionCenters G) (hr : 1 ≤ G.radius.toNat)
    (hpos : ∀ c, 0 < (F.path c).length) :
    ∃ L, 0 < L ∧ ∀ c, (F.path c).length = L := by
  haveI : Nonempty ↥(K : Set α) := hK.nonempty
  let a : ↥(K : Set α) := Classical.choice inferInstance
  refine ⟨(F.path a).length, hpos a, ?_⟩
  have hedge (u v : ↥(K : Set α)) (huv : (G.induce (K : Set α)).Adj u v) :
      (F.path u).length = (F.path v).length :=
    Nat.le_antisymm (F.length_le_of_adj hG hcard hdelete hr hpos v u huv.symm)
      (F.length_le_of_adj hG hcard hdelete hr hpos u v huv)
  have hclosed : ∀ u ∈ {c : ↥(K : Set α) | (F.path c).length = (F.path a).length},
      ∀ v, (G.induce (K : Set α)).Adj u v → (F.path v).length = (F.path a).length := by
    intro u hu v huv
    exact (hedge u v huv).symm.trans hu
  intro c
  exact reachable_mem_of_adj_closed hclosed (hK a c) rfl
end WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
