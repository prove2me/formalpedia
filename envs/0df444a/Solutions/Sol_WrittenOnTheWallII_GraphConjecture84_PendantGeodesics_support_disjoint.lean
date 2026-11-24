-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.support_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:29:59.091798+00:00
-- url     : https://prove2.me/submissions/ded3a245-e191-4c2e-b53c-3ce38cdccf24

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
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
theorem _root_.solution (hG : G.Connected) {c d : ↥(K : Set α)} (hcd : c ≠ d) :
    Disjoint (F.path c).support.toFinset (F.path d).support.toFinset := by
  apply Finset.disjoint_left.mpr
  intro z hz hd
  have h₁ := F.dist_from_core hG c d (List.mem_toFinset.mp hz)
  have h₂ := F.dist_from_core hG d c (List.mem_toFinset.mp hd)
  have hcomm : G.dist (d : α) c = G.dist c d := G.dist_comm
  have hzero : G.dist (c : α) d = 0 := by omega
  exact hcd (Subtype.ext (hG.dist_eq_zero_iff.mp hzero))
end WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
