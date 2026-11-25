-- Prove2me | solution 1 for SimpleGraph.Reservoir.card_pivot_pool
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:28:03.768636+00:00
-- url     : https://prove2.me/submissions/8d82e5d2-7741-4267-8a6d-89f75949a219

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
theorem _root_.solution : #(R.pivot v hv).pool + #{w ∈ R.pool | ¬G.Adj v w} = #R.pool :=
  card_filter_add_card_filter_not _
end SimpleGraph.Reservoir
