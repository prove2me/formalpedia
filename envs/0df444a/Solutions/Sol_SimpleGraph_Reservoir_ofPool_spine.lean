-- Prove2me | solution 1 for SimpleGraph.Reservoir.ofPool_spine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:26:28.784985+00:00
-- url     : https://prove2.me/submissions/b13ec164-4830-4a01-a08f-8c6f45b6deda

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
theorem _root_.solution (X : Finset V) : (ofPool (G := G) X).spine = ∅ := rfl
end SimpleGraph.Reservoir
