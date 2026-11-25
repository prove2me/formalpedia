-- Prove2me | solution 1 for SimpleGraph.Bireservoir.toBlue_pool
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:29:20.292444+00:00
-- url     : https://prove2.me/submissions/e5495302-e219-4ed5-83b5-03b1464a052a

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
variable (S : G.Bireservoir)
namespace SimpleGraph.Bireservoir
theorem _root_.solution : S.toBlue.pool = S.pool := rfl
end SimpleGraph.Bireservoir
