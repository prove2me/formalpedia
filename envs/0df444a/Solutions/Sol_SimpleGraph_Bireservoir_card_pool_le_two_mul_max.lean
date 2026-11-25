-- Prove2me | solution 1 for SimpleGraph.Bireservoir.card_pool_le_two_mul_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:34:29.840796+00:00
-- url     : https://prove2.me/submissions/f160a04b-8b9a-47af-a091-69181eec13a5

module
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Definitions.Def_RamseyReservoir_Reservoir
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Definitions.Def_RamseyReservoir_Bireservoir
public import Theorems.Thm_SimpleGraph_Bireservoir_card_redPivot_pool_add_card_bluePivot_pool

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
theorem _root_.solution :
    #S.pool ≤ 2 * max #(S.redPivot hv).pool #(S.bluePivot hv).pool + 1 := by
  have := S.card_redPivot_pool_add_card_bluePivot_pool hv
  omega
end SimpleGraph.Bireservoir
