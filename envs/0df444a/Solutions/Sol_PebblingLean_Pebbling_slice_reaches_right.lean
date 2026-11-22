-- Prove2me | solution 1 for PebblingLean.Pebbling.slice_reaches_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:53:24.958661+00:00
-- url     : https://prove2.me/submissions/db144c08-91bc-4773-b998-bd9510e60d69

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_PebblingLean_Product
public import Theorems.Thm_PebblingLean_Pebbling_slice_move_right

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u v
open PebblingLean.Pebbling
variable {V : Type u} {W : Type v}
namespace PebblingLean.Pebbling
theorem _root_.solution [DecidableEq V] [DecidableEq W] {G : Graph V} {H : Graph W}
    {E F : Pebbling W} {x : V}
    (hreach : Reaches H E F) :
    Reaches (Graph.cartesianProduct G H) (sliceDistribution x E) (sliceDistribution x F) := by
  unfold Reaches at hreach ⊢
  refine hreach.head_induction_on ?refl ?head
  · exact Relation.ReflTransGen.refl
  · intro A B hmove _ hslice
    exact Relation.ReflTransGen.head (slice_move_right (G := G) (H := H) (x := x) hmove) hslice
end PebblingLean.Pebbling
