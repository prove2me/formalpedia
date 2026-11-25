-- Prove2me | solution 1 for SimpleGraph.Reservoir.card_pivot_spine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:27:10.747014+00:00
-- url     : https://prove2.me/submissions/f3686dae-0011-4da1-b9b1-187090400bda

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Definitions.Def_RamseyReservoir_Reservoir
public import Theorems.Thm_SimpleGraph_Reservoir_not_mem_spine_of_mem_pool

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
theorem _root_.solution : #(R.pivot v hv).spine = #R.spine + 1 :=
  card_insert_of_notMem (R.not_mem_spine_of_mem_pool hv)
end SimpleGraph.Reservoir
