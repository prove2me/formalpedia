-- Prove2me | solution 1 for QEC.Bounds.BPTSquareLattice.tileIndex_eq_of_mem_squarePartitionBComponent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:37:11.936634+00:00
-- url     : https://prove2.me/submissions/468d9b89-a658-4c37-b703-d6814109b754

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_SquarePartition
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_tileIndex_eq_of_mem_tile
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_mem_squarePartitionBComponent_iff

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
    (hsite : site ∈ L.squarePartitionBComponent blockWidth margin index) :
    L.tileIndex blockWidth site = index :=
  L.tileIndex_eq_of_mem_tile hblockWidth (L.mem_squarePartitionBComponent_iff
    blockWidth margin index site |>.mp hsite).1
end QEC.Bounds.BPTSquareLattice
