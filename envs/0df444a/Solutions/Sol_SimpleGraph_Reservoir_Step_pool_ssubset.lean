-- Prove2me | solution 1 for SimpleGraph.Reservoir.Step.pool_ssubset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:27:16.724195+00:00
-- url     : https://prove2.me/submissions/f299811d-5bba-4afd-ad05-2b5351dbfa85

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
variable [DecidableEq V] [DecidableRel G.Adj]
namespace SimpleGraph.Reservoir
namespace Step
theorem _root_.solution {R R' : G.Reservoir} (h : Step R R') : R'.pool ⊂ R.pool := by
  obtain ⟨v, hv, -, hp⟩ := h
  rw [hp]
  exact (filter_ssubset).mpr ⟨v, hv, G.irrefl⟩
end Step
end SimpleGraph.Reservoir
