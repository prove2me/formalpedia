-- Prove2me | solution 1 for SimpleGraph.Bireservoir.ofPool_red
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:29:09.82385+00:00
-- url     : https://prove2.me/submissions/75219d38-54dd-4b64-ab6d-e695d7ad9d0f

module
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Definitions.Def_RamseyReservoir_Reservoir
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Definitions.Def_RamseyReservoir_Bireservoir

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
open SimpleGraph.Bireservoir
variable {G}
namespace SimpleGraph.Bireservoir
theorem _root_.solution (X : Finset V) : (ofPool (G := G) X).red = ∅ := rfl
end SimpleGraph.Bireservoir
