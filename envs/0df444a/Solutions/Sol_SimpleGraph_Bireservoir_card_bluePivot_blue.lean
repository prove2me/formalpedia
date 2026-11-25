-- Prove2me | solution 1 for SimpleGraph.Bireservoir.card_bluePivot_blue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:31:28.187668+00:00
-- url     : https://prove2.me/submissions/19fc7a82-aeec-4081-9193-555f6e9ecb37

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
theorem _root_.solution : #(S.bluePivot hv).blue = #S.blue + 1 :=
  S.toBlue.card_pivot_spine hv
end SimpleGraph.Bireservoir
