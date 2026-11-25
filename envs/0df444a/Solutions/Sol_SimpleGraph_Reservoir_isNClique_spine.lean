-- Prove2me | solution 1 for SimpleGraph.Reservoir.isNClique_spine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:33:16.455113+00:00
-- url     : https://prove2.me/submissions/628f3fca-b92c-4b0a-9ab1-0ae331defd8e

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
variable (R : G.Reservoir)
namespace SimpleGraph.Reservoir
theorem _root_.solution : G.IsNClique #R.spine R.spine := ⟨R.isClique_spine, rfl⟩
end SimpleGraph.Reservoir
