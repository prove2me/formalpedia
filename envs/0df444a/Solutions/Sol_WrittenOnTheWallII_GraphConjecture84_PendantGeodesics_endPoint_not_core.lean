-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.endPoint_not_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:30:07.151385+00:00
-- url     : https://prove2.me/submissions/38ae4481-c898-4b64-8310-babb294ffae5

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_length_pos_iff

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
open WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
variable {G : SimpleGraph α} {K : Finset α} (F : PendantGeodesics G K)
namespace WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
theorem _root_.solution (hG : G.Connected) (c : ↥(K : Set α))
    (hpos : 0 < (F.path c).length) : F.endPoint c ∉ K := by
  intro heK
  exact (F.length_pos_iff hG c).mp hpos
    (F.core_inter c _ (F.path c).end_mem_support heK)
end WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
