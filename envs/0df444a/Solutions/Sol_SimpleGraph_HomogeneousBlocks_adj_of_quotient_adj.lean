-- Prove2me | solution 1 for SimpleGraph.HomogeneousBlocks.adj_of_quotient_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:27:59.289158+00:00
-- url     : https://prove2.me/submissions/aee48148-6d10-46e6-98e6-3a2fb0e1d199

module
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Definitions.Def_RamseyReservoir_Reservoir
public import Definitions.Def_RamseyReservoir_HomogeneousBlocks
public import Theorems.Thm_SimpleGraph_HomogeneousBlocks_quotient_adj

set_option autoImplicit true
@[expose] public section
public section
open Finset Function
open SimpleGraph
variable {V ι : Type*}
open SimpleGraph.HomogeneousBlocks
variable {G : SimpleGraph V} (F : G.HomogeneousBlocks ι)
namespace SimpleGraph.HomogeneousBlocks
theorem _root_.solution {i j : ι} (h : F.quotient.Adj i j) {x y : V} (hx : x ∈ F.block i)
    (hy : y ∈ F.block j) : G.Adj x y :=
  (F.quotient_adj.mp h).2 x hx y hy
end SimpleGraph.HomogeneousBlocks
