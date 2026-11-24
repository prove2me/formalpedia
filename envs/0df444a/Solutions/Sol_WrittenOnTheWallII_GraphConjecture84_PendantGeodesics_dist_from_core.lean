-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.dist_from_core
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:27:10.282153+00:00
-- url     : https://prove2.me/submissions/6bc7e389-651b-4c7e-aba6-21d9bad0f55c

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_dist_eq_add_of_not_reachable_compl
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_tail_separated

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
open WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
variable {G : SimpleGraph α} {K : Finset α} (F : PendantGeodesics G K)
namespace WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
theorem _root_.solution (hG : G.Connected) (c v : ↥(K : Set α)) {z : α}
    (hz : z ∈ (F.path c).support) :
    G.dist v z = G.dist v c + G.dist c z := by
  by_cases hvc : (v : α) = (c : α)
  · simp [hvc]
  by_cases hzc : z = (c : α)
  · simp [hzc]
  have hv : (v : α) ∉ (F.path c).support := fun hv => hvc (F.core_inter c v hv v.property)
  apply dist_eq_add_of_not_reachable_compl hG hvc hzc
  exact fun hr => F.tail_separated c hz hzc hv hr.symm
end WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
