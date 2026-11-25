-- Prove2me | solution 1 for SimpleGraph.HomogeneousBlocks.repEmbedding_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:32:55.396873+00:00
-- url     : https://prove2.me/submissions/482672d5-3d0f-43d9-983c-0ca5c5524466

module
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Definitions.Def_RamseyReservoir_Reservoir
public import Definitions.Def_RamseyReservoir_HomogeneousBlocks

set_option autoImplicit true
@[expose] public section
public section
open Finset Function
open SimpleGraph
variable {V ι : Type*}
open SimpleGraph.HomogeneousBlocks
variable {G : SimpleGraph V} (F : G.HomogeneousBlocks ι)
namespace SimpleGraph.HomogeneousBlocks
theorem _root_.solution (i : ι) : F.repEmbedding i = F.rep i := rfl
end SimpleGraph.HomogeneousBlocks
