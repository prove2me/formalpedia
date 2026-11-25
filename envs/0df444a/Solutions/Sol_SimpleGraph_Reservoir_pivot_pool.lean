-- Prove2me | solution 1 for SimpleGraph.Reservoir.pivot_pool
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:26:32.421894+00:00
-- url     : https://prove2.me/submissions/02638fc1-8bea-4199-9ff3-a1e4233ab2bc

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
theorem _root_.solution : (R.pivot v hv).pool = {w ∈ R.pool | G.Adj v w} := rfl
end SimpleGraph.Reservoir
