-- Prove2me | solution 1 for QEC.Bounds.BPTSquareLattice.CoordinateRangeSeparated.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:25:31.74518+00:00
-- url     : https://prove2.me/submissions/f216050b-032f-4659-80a9-d48c337b7d49

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
    {left' left right' right : Finset L.Site}
    (hgap : L.CoordinateRangeSeparated range left right) (hleft : left' ⊆ left)
    (hright : right' ⊆ right) :
    L.CoordinateRangeSeparated range left' right' := by
  intro leftSite hleftSite rightSite hrightSite
  exact hgap leftSite (hleft hleftSite) rightSite (hright hrightSite)
end CoordinateRangeSeparated
end QEC.Bounds.BPTSquareLattice
