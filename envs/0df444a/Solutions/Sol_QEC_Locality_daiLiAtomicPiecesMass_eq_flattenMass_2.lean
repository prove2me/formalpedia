-- Prove2me | solution 2 for QEC.Locality.daiLiAtomicPiecesMass_eq_flattenMass
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:29:47.983815+00:00
-- url     : https://prove2.me/submissions/d4b3c742-d77c-42e7-b027-c783a7bc4269

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
    daiLiAtomicPiecesMass pieces = daiLiAtomicMass pieces.flatten := by
  unfold daiLiAtomicPiecesMass daiLiAtomicMass
  rw [List.sum_flatten]
