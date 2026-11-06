-- Prove2me | solution 2 for QEC.Locality.daiLiAtomicPiecesMass_reverse
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:29:47.085202+00:00
-- url     : https://prove2.me/submissions/9e67b1b2-451d-4ee6-a6b7-08c2e9d849a3

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ]

theorem solution (pieces : List (List DaiLiAtomicCounter)) :
    daiLiAtomicPiecesMass pieces.reverse = daiLiAtomicPiecesMass pieces := by
  unfold daiLiAtomicPiecesMass
  rw [List.map_reverse, List.sum_reverse]
