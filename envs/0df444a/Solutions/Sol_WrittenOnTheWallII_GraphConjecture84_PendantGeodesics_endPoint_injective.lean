-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.endPoint_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:35:09.906514+00:00
-- url     : https://prove2.me/submissions/b2cd5ff5-42c9-4542-9a5f-70fcf89e923a

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_support_disjoint

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
open WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
variable {G : SimpleGraph α} {K : Finset α} (F : PendantGeodesics G K)
namespace WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
theorem _root_.solution (hG : G.Connected) : Function.Injective F.endPoint := by
  intro c d heq
  by_contra hcd
  exact (Finset.disjoint_left.mp (F.support_disjoint hG hcd))
    (by simpa only [List.mem_toFinset] using (F.path c).end_mem_support)
    (by simpa only [List.mem_toFinset, heq] using (F.path d).end_mem_support)
end WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
