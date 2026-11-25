-- Prove2me | solution 1 for SimpleGraph.Reservoir.pivot_spine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:26:31.21272+00:00
-- url     : https://prove2.me/submissions/5dd8f761-d18b-40bf-89be-299a2b5700d1

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
variable [DecidableRel G.Adj] [DecidableEq V]
variable {v : V} (hv : v ∈ R.pool)
namespace SimpleGraph.Reservoir
theorem _root_.solution : (R.pivot v hv).spine = insert v R.spine := rfl
end SimpleGraph.Reservoir
