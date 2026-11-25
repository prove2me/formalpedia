-- Prove2me | solution 1 for SimpleGraph.Reservoir.Reaches.spine_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:33:42.786921+00:00
-- url     : https://prove2.me/submissions/28488057-541e-409e-a606-0a202a1fb880

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
namespace Reaches
theorem _root_.solution {R R' : G.Reservoir} (h : Reaches R R') : R.spine ⊆ R'.spine := by
  induction h with
  | refl => exact Subset.rfl
  | tail _ h ih =>
    obtain ⟨v, -, hs, -⟩ := h
    exact ih.trans (hs ▸ subset_insert _ _)
end Reaches
end SimpleGraph.Reservoir
