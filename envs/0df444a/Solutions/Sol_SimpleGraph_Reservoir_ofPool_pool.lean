-- Prove2me | solution 1 for SimpleGraph.Reservoir.ofPool_pool
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:26:30.370653+00:00
-- url     : https://prove2.me/submissions/9bb816f5-5aa0-43e4-997a-982e70af49f0

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
theorem _root_.solution (X : Finset V) : (ofPool (G := G) X).pool = X := rfl
end SimpleGraph.Reservoir
