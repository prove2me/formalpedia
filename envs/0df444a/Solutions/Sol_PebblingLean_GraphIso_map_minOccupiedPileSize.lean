-- Prove2me | solution 1 for PebblingLean.GraphIso.map_minOccupiedPileSize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:51:08.20897+00:00
-- url     : https://prove2.me/submissions/a0ed0d02-8382-42f9-9707-ff4155e8e829

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_PebblingLean_GraphIso

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u v
open PebblingLean.GraphIso
variable {V : Type u} {W : Type v} {G : Graph V} {H : Graph W}
namespace PebblingLean.GraphIso
theorem _root_.solution (iso : GraphIso G H) {D : Pebbling V} {S : ℕ}
    (hmin : Pebbling.MinOccupiedPileSize D S) :
    Pebbling.MinOccupiedPileSize (iso.mapDistribution D) S := by
  intro w hw
  exact hmin (iso.toEquiv.symm w) hw
end PebblingLean.GraphIso
