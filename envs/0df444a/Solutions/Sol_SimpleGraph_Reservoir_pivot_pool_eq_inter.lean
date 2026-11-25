-- Prove2me | solution 1 for SimpleGraph.Reservoir.pivot_pool_eq_inter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:33:24.251218+00:00
-- url     : https://prove2.me/submissions/d60479bf-6048-4012-8c01-055e7300290d

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Definitions.Def_RamseyReservoir_Reservoir
public import Theorems.Thm_SimpleGraph_Reservoir_ofPool_spine
public import Theorems.Thm_SimpleGraph_Reservoir_ofPool_pool
public import Theorems.Thm_SimpleGraph_Reservoir_pivot_spine
public import Theorems.Thm_SimpleGraph_Reservoir_pivot_pool
attribute [local simp] SimpleGraph.Reservoir.ofPool_spine
attribute [local simp] SimpleGraph.Reservoir.ofPool_pool
attribute [local simp] SimpleGraph.Reservoir.pivot_spine
attribute [local simp] SimpleGraph.Reservoir.pivot_pool

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
theorem _root_.solution [Fintype (G.neighborSet v)] :
    (R.pivot v hv).pool = R.pool ∩ G.neighborFinset v := by
  ext w
  simp
end SimpleGraph.Reservoir
