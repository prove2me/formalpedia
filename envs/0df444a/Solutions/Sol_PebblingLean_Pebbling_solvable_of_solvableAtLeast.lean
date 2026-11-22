-- Prove2me | solution 1 for PebblingLean.Pebbling.solvable_of_solvableAtLeast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:48:30.560805+00:00
-- url     : https://prove2.me/submissions/bf973ba1-9f0d-4da7-aa93-f9077befe811

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Theorems.Thm_PebblingLean_Pebbling_solvableAtLeast_mono

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u
open PebblingLean.Pebbling
variable {V : Type u}
namespace PebblingLean.Pebbling
theorem _root_.solution [DecidableEq V] {G : Graph V} {D : Pebbling V}
    {T : ℕ} (hT : 1 ≤ T) (hsolv : SolvableAtLeast G D T) :
    Solvable G D :=
  solvableAtLeast_mono hT hsolv
end PebblingLean.Pebbling
