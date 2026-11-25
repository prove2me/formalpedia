-- Prove2me | solution 1 for SimpleGraph.Bireservoir.ofPool_blue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:29:11.174365+00:00
-- url     : https://prove2.me/submissions/5576788f-38e1-442c-998c-5ab472ed0f1d

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
theorem _root_.solution (X : Finset V) : (ofPool (G := G) X).blue = ∅ := rfl
end SimpleGraph.Bireservoir
