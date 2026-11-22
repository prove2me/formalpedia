-- Prove2me | solution 1 for PebblingLean.GraphIso.map_canReachAtLeast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:53:57.020326+00:00
-- url     : https://prove2.me/submissions/e70c50c9-e1fb-4670-a03b-86b43f49f184

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_PebblingLean_GraphIso
public import Theorems.Thm_PebblingLean_GraphIso_map_reaches
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
theorem _root_.solution [DecidableEq V] [DecidableEq W]
    (iso : GraphIso G H) {D : Pebbling V} {target : W} {T : ℕ}
    (hcan : Pebbling.CanReachAtLeast G D (iso.toEquiv.symm target) T) :
    Pebbling.CanReachAtLeast H (iso.mapDistribution D) target T := by
  rcases hcan with ⟨E, hreach, htarget⟩
  refine ⟨iso.mapDistribution E, iso.map_reaches hreach, ?_⟩
  simpa [mapDistribution] using htarget
end PebblingLean.GraphIso
