-- Prove2me | solution 1 for PebblingLean.GraphIso.map_hasSolvableAtMostSize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:03:33.901192+00:00
-- url     : https://prove2.me/submissions/7ee7344f-8fd3-416c-83fb-b8dc58a5017d

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_PebblingLean_GraphIso
public import Theorems.Thm_PebblingLean_GraphIso_size_mapDistribution
public import Theorems.Thm_PebblingLean_GraphIso_map_solvableAtLeast
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_from
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_of_ne
public import Theorems.Thm_PebblingLean_Pebbling_moveDistribution_apply_to
public import Theorems.Thm_PebblingLean_Pebbling_size_zero
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_from
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_of_ne
attribute [local simp] PebblingLean.Pebbling.moveDistribution_apply_to
attribute [local simp] PebblingLean.Pebbling.size_zero



set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u v
open PebblingLean.GraphIso
variable {V : Type u} {W : Type v} {G : Graph V} {H : Graph W}
namespace PebblingLean.GraphIso
theorem _root_.solution [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
    (iso : GraphIso G H) {T k : ℕ}
    (h : Pebbling.HasSolvableAtMostSize G T k) :
    Pebbling.HasSolvableAtMostSize H T k := by
  rcases h with ⟨D, hsize, hsolv⟩
  refine ⟨iso.mapDistribution D, ?_, iso.map_solvableAtLeast hsolv⟩
  simpa [iso.size_mapDistribution D] using hsize
end PebblingLean.GraphIso
