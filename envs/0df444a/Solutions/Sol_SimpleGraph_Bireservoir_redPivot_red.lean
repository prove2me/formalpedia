-- Prove2me | solution 1 for SimpleGraph.Bireservoir.redPivot_red
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:29:25.777815+00:00
-- url     : https://prove2.me/submissions/f11e6d60-e55b-422b-a0d9-b56c38a54ebf

module
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Definitions.Def_RamseyReservoir_Reservoir
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Definitions.Def_RamseyReservoir_Bireservoir

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
theorem _root_.solution : (S.redPivot hv).red = insert v S.red := rfl
end SimpleGraph.Bireservoir
