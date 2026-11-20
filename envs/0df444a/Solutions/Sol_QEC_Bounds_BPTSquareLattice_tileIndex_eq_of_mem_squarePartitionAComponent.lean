-- Prove2me | solution 1 for QEC.Bounds.BPTSquareLattice.tileIndex_eq_of_mem_squarePartitionAComponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:43:08.095058+00:00
-- url     : https://prove2.me/submissions/8c1bc3e3-f84a-4a6c-bd3d-ad1d73ae29a6

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_SquarePartition
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_tileIndex_eq_of_mem_tile
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_mem_squarePartitionAComponent_iff

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open Semantics
universe u v
open QEC.Bounds.BPTSquareLattice
namespace QEC.Bounds.BPTSquareLattice
theorem _root_.solution (L : BPTSquareLattice)
    {blockWidth : Nat} (hblockWidth : 0 < blockWidth) (margin : Nat)
    {index : Nat × Nat} {site : L.Site}
    (hsite : site ∈ L.squarePartitionAComponent blockWidth margin index) :
    L.tileIndex blockWidth site = index :=
  L.tileIndex_eq_of_mem_tile hblockWidth (L.mem_squarePartitionAComponent_iff
    blockWidth margin index site |>.mp hsite).1
end QEC.Bounds.BPTSquareLattice
