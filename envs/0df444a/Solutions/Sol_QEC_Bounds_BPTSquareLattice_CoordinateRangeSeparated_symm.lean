-- Prove2me | solution 1 for QEC.Bounds.BPTSquareLattice.CoordinateRangeSeparated.symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:19:39.520093+00:00
-- url     : https://prove2.me/submissions/11f67ef6-3763-4d3d-b63a-b1f23b7858d6

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
namespace CoordinateRangeSeparated
theorem _root_.solution (L : BPTSquareLattice) {range : Nat}
    {left right : Finset L.Site}
    (hgap : L.CoordinateRangeSeparated range left right) :
    L.CoordinateRangeSeparated range right left := by
  intro rightSite hrightSite leftSite hleftSite
  rcases hgap leftSite hleftSite rightSite hrightSite with hrow | hrow | hcolumn | hcolumn
  · exact Or.inr (Or.inl hrow)
  · exact Or.inl hrow
  · exact Or.inr (Or.inr (Or.inr hcolumn))
  · exact Or.inr (Or.inr (Or.inl hcolumn))
end CoordinateRangeSeparated
end QEC.Bounds.BPTSquareLattice
