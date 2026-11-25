-- Prove2me | solution 1 for SimpleGraph.Bireservoir.redPivot_pool
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:29:31.771845+00:00
-- url     : https://prove2.me/submissions/45e2153b-34fc-4a3f-87c7-ede48c142f2a

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
theorem _root_.solution : (S.redPivot hv).pool = {w ∈ S.pool | G.Adj v w} := rfl
end SimpleGraph.Bireservoir
