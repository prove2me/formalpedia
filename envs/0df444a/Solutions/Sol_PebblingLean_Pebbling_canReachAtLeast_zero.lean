-- Prove2me | solution 1 for PebblingLean.Pebbling.canReachAtLeast_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:46:33.431476+00:00
-- url     : https://prove2.me/submissions/bdc87201-20b4-450e-ac48-97c1d8e6cf95

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_PebblingLean_Basic

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Pebbling
variable {V : Type u}
namespace PebblingLean.Pebbling
theorem _root_.solution [DecidableEq V] (G : Graph V) (D : Pebbling V) (target : V) :
    CanReachAtLeast G D target 0 :=
  ⟨D, Relation.ReflTransGen.refl, Nat.zero_le _⟩
end PebblingLean.Pebbling
