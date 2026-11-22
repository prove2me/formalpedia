-- Prove2me | solution 1 for PebblingLean.Pebbling.hasSolvableAtMostSize_mono_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:46:35.584344+00:00
-- url     : https://prove2.me/submissions/adb27a63-3116-4c3a-9c82-25c4aca6fd9b

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
theorem _root_.solution [Fintype V] [DecidableEq V]
    {G : Graph V} {T k k' : ℕ} (hkk' : k ≤ k')
    (h : HasSolvableAtMostSize G T k) :
    HasSolvableAtMostSize G T k' := by
  rcases h with ⟨D, hsize, hsolv⟩
  exact ⟨D, hsize.trans hkk', hsolv⟩
end PebblingLean.Pebbling
