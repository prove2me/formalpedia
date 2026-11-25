-- Prove2me | solution 1 for SimpleGraph.Reservoir.step_pivot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:33:28.68307+00:00
-- url     : https://prove2.me/submissions/5371a75c-24ad-410c-90b1-fd5fcfd7b05e

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
theorem _root_.solution {v : V} (hv : v ∈ R.pool) : Step R (R.pivot v hv) := ⟨v, hv, rfl, rfl⟩
end SimpleGraph.Reservoir
