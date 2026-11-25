-- Prove2me | solution 1 for SimpleGraph.IsClique.union_of_forall_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:27:14.684556+00:00
-- url     : https://prove2.me/submissions/cecf28c6-8ffb-4111-86e7-13f1fadb54bb

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Definitions.Def_RamseyReservoir_Reservoir

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
open SimpleGraph.Reservoir
variable {G}
namespace SimpleGraph.Reservoir
namespace _root_.SimpleGraph.IsClique
theorem _root_.solution {s t : Set V} (hs : G.IsClique s)
    (ht : G.IsClique t) (h : ∀ x ∈ s, ∀ y ∈ t, G.Adj x y) : G.IsClique (s ∪ t) := by
  rintro x (hx | hx) y (hy | hy) hxy
  exacts [hs hx hy hxy, h x hx y hy, (h y hy x hx).symm, ht hx hy hxy]
end _root_.SimpleGraph.IsClique
end SimpleGraph.Reservoir
