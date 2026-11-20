-- Prove2me | solution 1 for QEC.Bounds.BPTSquareLattice.coordinateRangeSeparated_squarePartitionAComponent_diagonal_succ_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:43:52.825224+00:00
-- url     : https://prove2.me/submissions/4a3ffa3e-aa7e-47d5-8df1-f5648d8d48f0

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_SquarePartition
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_mem_squarePartitionAComponent_iff
import Theorems.Thm_QEC_Bounds_BPTSquareLattice_coordinateRangeSeparated_of_cornerCutout_diagonal_succ_succ

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Bounds
open Classical
open Semantics
universe u v
open QEC.Bounds.BPTSquareLattice
namespace QEC.Bounds.BPTSquareLattice
theorem _root_.solution
    (L : BPTSquareLattice) {blockWidth margin range : Nat}
    (hblockWidth : 0 < blockWidth) (hrange : range ≤ margin)
    (index : Nat × Nat) :
    L.CoordinateRangeSeparated range
      (L.squarePartitionAComponent blockWidth margin index)
      (L.squarePartitionAComponent blockWidth margin (index.1 + 1, index.2 + 1)) := by
  apply L.coordinateRangeSeparated_of_cornerCutout_diagonal_succ_succ
    hblockWidth hrange index
  · intro site hsite
    exact (L.mem_squarePartitionAComponent_iff blockWidth margin index site |>.mp hsite).1
  · intro site hsite
    exact (L.mem_squarePartitionAComponent_iff blockWidth margin index site |>.mp hsite).2.1
  · intro site hsite
    exact (L.mem_squarePartitionAComponent_iff blockWidth margin
      (index.1 + 1, index.2 + 1) site |>.mp hsite).1
end QEC.Bounds.BPTSquareLattice
