-- Prove2me | solution 1 for PebblingLean.Pebbling.le_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:46:33.040378+00:00
-- url     : https://prove2.me/submissions/77b0efab-b385-404c-8fbe-ac1e4cd8bfb2

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
theorem _root_.solution [Fintype V] (D : Pebbling V) (v : V) :
    D v ≤ size D := by
  classical
  rw [size]
  exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)
end PebblingLean.Pebbling
