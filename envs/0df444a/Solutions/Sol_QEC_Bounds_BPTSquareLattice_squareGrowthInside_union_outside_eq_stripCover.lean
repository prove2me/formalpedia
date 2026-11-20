-- Prove2me | solution 1 for QEC.Bounds.BPTSquareLattice.squareGrowthInside_union_outside_eq_stripCover
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:25:28.51319+00:00
-- url     : https://prove2.me/submissions/0ed48d81-8cbb-4318-a530-174cc7c65475

import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_BlockRecursion
import Definitions.Def_QEC_Bounds_BPTSeparatedUnion
import Definitions.Def_QEC_Bounds_GeometricLocalityTradeoff_SquarePartition

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
    (origin : Nat × Nat) (width margin : Nat) :
    L.squareGrowthInside origin width margin ∪ L.squareGrowthOutside origin width margin =
      L.squareBoundaryFrameStripCover origin width margin := by
  change (L.square origin width ∩ L.squareBoundaryFrameStripCover origin width margin) ∪
      (L.squareBoundaryFrameStripCover origin width margin \ L.square origin width) =
        L.squareBoundaryFrameStripCover origin width margin
  rw [Finset.inter_comm, Finset.union_comm]
  exact Finset.sdiff_union_inter _ _
end QEC.Bounds.BPTSquareLattice
