-- Prove2me | solution 1 for SimpleGraph.Reservoir.Reaches.card_add_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:33:52.388965+00:00
-- url     : https://prove2.me/submissions/506b250d-0453-46e8-ac15-1e3e86ec72c5

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Definitions.Def_RamseyReservoir_Reservoir
public import Theorems.Thm_SimpleGraph_Reservoir_Step_card_spine
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
theorem _root_.solution {R R' : G.Reservoir} (h : Reaches R R') :
    #R'.spine + #R'.pool ≤ #R.spine + #R.pool := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih =>
    have := card_lt_card h.pool_ssubset
    rw [h.card_spine]
    omega
end Reaches
end SimpleGraph.Reservoir
