-- Prove2me | solution 1 for SimpleGraph.ramseyBound_six_three_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:36:24.109988+00:00
-- url     : https://prove2.me/submissions/88bdd13d-4ac9-4444-a646-db32bf512f34

module
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Definitions.Def_RamseyReservoir_Reservoir
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Definitions.Def_RamseyReservoir_Bireservoir
public import Theorems.Thm_SimpleGraph_ramseyBound_choose

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
namespace SimpleGraph
theorem _root_.solution : RamseyBound 6 3 3 := ramseyBound_choose 2 2
end SimpleGraph
