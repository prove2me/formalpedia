-- Prove2me | solution 1 for QEC.Locality.daiLiPhysicalGreedySubdivision_infix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:57:02.347076+00:00
-- url     : https://prove2.me/submissions/051ec52a-54a3-45c3-bc5c-430cfeb433a0

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Theorems.Thm_QEC_Locality_daiLiPhysicalGreedySubdivision_join
import Theorems.Thm_QEC_Locality_daiLiGroup_infix_flatten

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ]
namespace QEC.Locality
theorem _root_.solution
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right : ℝ)
    (d : Nat) (atoms piece : List (ℝ × ℝ))
    (hPiece : piece ∈ daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms) :
    piece <:+: atoms := by
  rw [← daiLiPhysicalGreedySubdivision_join P embedding threshold left right d atoms]
  exact daiLiGroup_infix_flatten
    (daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms) piece hPiece
end QEC.Locality
