-- Prove2me | solution 1 for PebblingLean.Pebbling.fibersDistribution_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:47:52.997462+00:00
-- url     : https://prove2.me/submissions/af912d65-ff9e-41f7-9fb4-d58d6094c3f9

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Definitions.Def_LeanPool_PebblingLean_Product

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u v
open PebblingLean.Pebbling
variable {V : Type u} {W : Type v}
namespace PebblingLean.Pebbling
theorem _root_.solution (F : W → Pebbling V) (x : V) (z : W) :
    fibersDistribution F (x, z) = F z x :=
  rfl
end PebblingLean.Pebbling
