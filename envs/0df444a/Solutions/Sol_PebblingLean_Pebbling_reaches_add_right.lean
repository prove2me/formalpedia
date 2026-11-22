-- Prove2me | solution 1 for PebblingLean.Pebbling.reaches_add_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:03:33.080801+00:00
-- url     : https://prove2.me/submissions/b39ca8cd-c6dd-4d6c-af83-c2b7dd3cd5fc

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow
public import Definitions.Def_LeanPool_PebblingLean_Delivery
public import Theorems.Thm_PebblingLean_Pebbling_move_add_right

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Pebbling
variable {V : Type u}
namespace PebblingLean.Pebbling
theorem _root_.solution [DecidableEq V] {G : Graph V} {D E A : Pebbling V}
    (hreach : Reaches G D E) :
    Reaches G (D + A) (E + A) := by
  unfold Reaches at hreach ⊢
  refine hreach.head_induction_on ?refl ?head
  · exact Relation.ReflTransGen.refl
  · intro B C hmove _ ih
    exact Relation.ReflTransGen.head (move_add_right hmove) ih
end PebblingLean.Pebbling
