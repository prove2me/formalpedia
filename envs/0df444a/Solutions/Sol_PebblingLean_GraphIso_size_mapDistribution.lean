-- Prove2me | solution 1 for PebblingLean.GraphIso.size_mapDistribution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:50:10.948722+00:00
-- url     : https://prove2.me/submissions/7466a526-fbed-483f-89e8-fa8d60b5c27e

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
theorem _root_.solution [Fintype V] [Fintype W]
    (iso : GraphIso G H) (D : Pebbling V) :
    Pebbling.size (iso.mapDistribution D) = Pebbling.size D := by
  change (∑ w : W, D (iso.toEquiv.symm w)) = ∑ v : V, D v
  exact Equiv.sum_comp iso.toEquiv.symm D
end PebblingLean.GraphIso
