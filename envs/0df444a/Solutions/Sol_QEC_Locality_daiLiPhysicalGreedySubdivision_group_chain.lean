-- Prove2me | solution 1 for QEC.Locality.daiLiPhysicalGreedySubdivision_group_chain
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:21:15.078931+00:00
-- url     : https://prove2.me/submissions/f84e0346-5747-47bd-8e80-6d671fcaea87

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Theorems.Thm_QEC_Locality_DaiLiHorizontalAtomization_atom_chain
import Theorems.Thm_QEC_Locality_daiLiPhysicalGreedySubdivision_infix

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
    {ell lower upper : ℝ} {atoms piece : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding)
      ell lower upper atoms)
    (d : Nat)
    (hPiece : piece ∈ daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms) :
    piece.IsChain DaiLiAtomAdjacent := by
  exact hAtoms.atom_chain.infix
    (daiLiPhysicalGreedySubdivision_infix P embedding threshold left right d atoms piece hPiece)
end QEC.Locality
