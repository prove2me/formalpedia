-- Prove2me | solution 1 for PebblingLean.Pebbling.size_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:46:19.898012+00:00
-- url     : https://prove2.me/submissions/bc3fc6ef-7e35-446f-9673-d5d4a841acba

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
theorem _root_.solution [Fintype V] : size (fun _ : V => 0) = 0 := by
  simp [size]
end PebblingLean.Pebbling
