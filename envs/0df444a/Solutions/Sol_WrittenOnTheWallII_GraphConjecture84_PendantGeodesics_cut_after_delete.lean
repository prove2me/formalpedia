-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.PendantGeodesics.cut_after_delete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:30:43.586043+00:00
-- url     : https://prove2.me/submissions/4ae3e28d-a17b-4733-a220-2642a9e8ec2f

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_not_connected_induce_delete_of_separated_pair
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_PendantGeodesics_tail_separated
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
theorem _root_.solution (hG : G.Connected) (x : α) (c v : ↥(K : Set α))
    (hc : 0 < (F.path c).length) (hcx : (c : α) ≠ x)
    (hex : F.endPoint c ≠ x) (hvc : v ≠ c) (hvx : (v : α) ≠ x) :
    ∃ y, ¬ ((G.induce ({x}ᶜ : Set α)).induce
      ({y}ᶜ : Set ↥({x}ᶜ : Set α))).Connected := by
  have hec := (F.length_pos_iff hG c).mp hc
  have hvpath : (v : α) ∉ (F.path c).support := by
    intro hv
    exact hvc (Subtype.ext (F.core_inter c v hv v.property))
  have hsep := F.tail_separated c (F.path c).end_mem_support hec hvpath
  refine ⟨⟨c, by simpa using hcx⟩, ?_⟩
  exact not_connected_induce_delete_of_separated_pair
    (S := ({x}ᶜ : Set α)) hcx hex hvx hec
    (show (v : α) ≠ (c : α) from fun heq => hvc (Subtype.ext heq)) hsep
end WrittenOnTheWallII.GraphConjecture84.PendantGeodesics
