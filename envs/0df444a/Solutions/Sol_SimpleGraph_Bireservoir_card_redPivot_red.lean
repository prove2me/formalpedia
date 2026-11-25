-- Prove2me | solution 1 for SimpleGraph.Bireservoir.card_redPivot_red
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:31:24.570698+00:00
-- url     : https://prove2.me/submissions/18cf2a37-e01d-4b1f-8d37-c5bba9473303

module
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Definitions.Def_RamseyReservoir_Reservoir
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Definitions.Def_RamseyReservoir_Bireservoir
public import Theorems.Thm_SimpleGraph_Reservoir_card_pivot_spine


set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
open SimpleGraph.Bireservoir
variable {G}
variable (S : G.Bireservoir)
variable [DecidableEq V] [DecidableRel G.Adj] {v : V} (hv : v ∈ S.pool)
namespace SimpleGraph.Bireservoir
theorem _root_.solution : #(S.redPivot hv).red = #S.red + 1 :=
  S.toRed.card_pivot_spine hv
end SimpleGraph.Bireservoir
