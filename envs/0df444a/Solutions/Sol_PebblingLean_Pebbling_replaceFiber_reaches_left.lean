-- Prove2me | solution 1 for PebblingLean.Pebbling.replaceFiber_reaches_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:53:24.594+00:00
-- url     : https://prove2.me/submissions/1e75c4f7-d6b8-41b4-8eb7-a3f66242e97c

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_PebblingLean_Product
public import Theorems.Thm_PebblingLean_Pebbling_replaceFiber_move_left

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u v
open PebblingLean.Pebbling
variable {V : Type u} {W : Type v}
namespace PebblingLean.Pebbling
theorem _root_.solution [DecidableEq V] [DecidableEq W]
    {G : Graph V} {H : Graph W} {E F : Pebbling V} {Fs : W → Pebbling V} {z : W}
    (hreach : Reaches G E F) :
    Reaches (Graph.cartesianProduct G H)
      (fibersDistribution (replaceFiber Fs z E))
      (fibersDistribution (replaceFiber Fs z F)) := by
  unfold Reaches at hreach ⊢
  refine hreach.head_induction_on ?refl ?head
  · exact Relation.ReflTransGen.refl
  · intro A B hmove _ hfiber
    exact Relation.ReflTransGen.head
      (replaceFiber_move_left (G := G) (H := H) (Fs := Fs) (z := z) hmove) hfiber
end PebblingLean.Pebbling
