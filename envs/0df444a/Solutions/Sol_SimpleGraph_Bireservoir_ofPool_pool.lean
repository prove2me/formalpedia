-- Prove2me | solution 1 for SimpleGraph.Bireservoir.ofPool_pool
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:29:15.235514+00:00
-- url     : https://prove2.me/submissions/aff11082-b130-4b86-af96-20fb77063be0

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
theorem _root_.solution (X : Finset V) : (ofPool (G := G) X).pool = X := rfl
end SimpleGraph.Bireservoir
