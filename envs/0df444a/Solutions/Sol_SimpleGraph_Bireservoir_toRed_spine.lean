-- Prove2me | solution 1 for SimpleGraph.Bireservoir.toRed_spine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:28:38.94143+00:00
-- url     : https://prove2.me/submissions/b8056e03-1d11-4eda-9e04-63ddb99c4da6

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
theorem _root_.solution : S.toRed.spine = S.red := rfl
end SimpleGraph.Bireservoir
