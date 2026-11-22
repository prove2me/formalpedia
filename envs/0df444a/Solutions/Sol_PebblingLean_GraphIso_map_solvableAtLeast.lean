-- Prove2me | solution 1 for PebblingLean.GraphIso.map_solvableAtLeast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:54:37.781823+00:00
-- url     : https://prove2.me/submissions/dfbe04ac-b937-4432-9c23-70a0559e28d8

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_PebblingLean_GraphIso
public import Theorems.Thm_PebblingLean_GraphIso_map_canReachAtLeast

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u v
open PebblingLean.GraphIso
variable {V : Type u} {W : Type v} {G : Graph V} {H : Graph W}
namespace PebblingLean.GraphIso
theorem _root_.solution [DecidableEq V] [DecidableEq W]
    (iso : GraphIso G H) {D : Pebbling V} {T : ℕ}
    (hsolv : Pebbling.SolvableAtLeast G D T) :
    Pebbling.SolvableAtLeast H (iso.mapDistribution D) T := by
  intro target
  exact iso.map_canReachAtLeast (hsolv (iso.toEquiv.symm target))
end PebblingLean.GraphIso
