-- Prove2me | solution 1 for SimpleGraph.Reservoir.not_mem_spine_of_mem_pool
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:26:35.433388+00:00
-- url     : https://prove2.me/submissions/3da22393-7f7e-4ea8-8069-8d4a72e277f1

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
theorem _root_.solution {v : V} (hv : v ∈ R.pool) : v ∉ R.spine :=
  fun h => Finset.disjoint_left.mp R.disjoint h hv
end SimpleGraph.Reservoir
