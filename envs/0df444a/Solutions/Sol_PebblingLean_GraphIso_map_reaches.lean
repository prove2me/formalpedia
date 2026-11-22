-- Prove2me | solution 1 for PebblingLean.GraphIso.map_reaches
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:53:23.923518+00:00
-- url     : https://prove2.me/submissions/2b76dbe3-fbf9-41f3-baa0-f1a21b31a139

module
public import Definitions.Def_LeanPool_PebblingLean_Basic
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_PebblingLean_GraphIso
public import Theorems.Thm_PebblingLean_GraphIso_map_move

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
universe u v
open PebblingLean.GraphIso
variable {V : Type u} {W : Type v} {G : Graph V} {H : Graph W}
namespace PebblingLean.GraphIso
theorem _root_.solution [DecidableEq V] [DecidableEq W]
    (iso : GraphIso G H) {D E : Pebbling V}
    (hreach : Pebbling.Reaches G D E) :
    Pebbling.Reaches H (iso.mapDistribution D) (iso.mapDistribution E) := by
  unfold Pebbling.Reaches at hreach ⊢
  refine hreach.head_induction_on ?refl ?head
  · exact Relation.ReflTransGen.refl
  · intro A B hmove _ ih
    exact Relation.ReflTransGen.head (iso.map_move hmove) ih
end PebblingLean.GraphIso
