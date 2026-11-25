-- Prove2me | solution 1 for SimpleGraph.Reservoir.pivot_pool_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:28:00.487887+00:00
-- url     : https://prove2.me/submissions/77a3b96a-98d4-458a-b982-fa729197137d

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
theorem _root_.solution : (R.pivot v hv).pool ⊆ R.pool := filter_subset _ _
end SimpleGraph.Reservoir
