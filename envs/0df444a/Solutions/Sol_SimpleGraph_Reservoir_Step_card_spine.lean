-- Prove2me | solution 1 for SimpleGraph.Reservoir.Step.card_spine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:28:10.115807+00:00
-- url     : https://prove2.me/submissions/91b22485-14a7-486f-a232-2dea3c1c4e53

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
variable [DecidableEq V] [DecidableRel G.Adj]
namespace SimpleGraph.Reservoir
namespace Step
theorem _root_.solution {R R' : G.Reservoir} (h : Step R R') : #R'.spine = #R.spine + 1 := by
  obtain ⟨v, hv, hs, -⟩ := h
  rw [hs, card_insert_of_notMem (R.not_mem_spine_of_mem_pool hv)]
end Step
end SimpleGraph.Reservoir
