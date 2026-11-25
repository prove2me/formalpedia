-- Prove2me | solution 1 for SimpleGraph.Reservoir.Reaches.pool_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:33:51.799819+00:00
-- url     : https://prove2.me/submissions/0ca5fc50-4712-421e-8286-223af6cec980

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Definitions.Def_RamseyReservoir_Reservoir
public import Theorems.Thm_SimpleGraph_Reservoir_Step_pool_ssubset

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
open SimpleGraph.Reservoir
variable {G}
variable (R : G.Reservoir)
variable [DecidableEq V] [DecidableRel G.Adj]
namespace SimpleGraph.Reservoir
namespace Reaches
theorem _root_.solution {R R' : G.Reservoir} (h : Reaches R R') : R'.pool ⊆ R.pool := by
  induction h with
  | refl => exact Subset.rfl
  | tail _ h ih => exact h.pool_ssubset.subset.trans ih
end Reaches
end SimpleGraph.Reservoir
