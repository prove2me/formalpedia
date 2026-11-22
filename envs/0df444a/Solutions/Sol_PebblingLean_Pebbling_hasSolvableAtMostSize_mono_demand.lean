-- Prove2me | solution 1 for PebblingLean.Pebbling.hasSolvableAtMostSize_mono_demand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:48:31.163371+00:00
-- url     : https://prove2.me/submissions/0a6ba4c7-8fa6-403d-9632-128bd8647d73

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
theorem _root_.solution [Fintype V] [DecidableEq V]
    {G : Graph V} {T T' k : ℕ} (hTT' : T' ≤ T)
    (h : HasSolvableAtMostSize G T k) :
    HasSolvableAtMostSize G T' k := by
  rcases h with ⟨D, hsize, hsolv⟩
  exact ⟨D, hsize, solvableAtLeast_mono hTT' hsolv⟩
end PebblingLean.Pebbling
