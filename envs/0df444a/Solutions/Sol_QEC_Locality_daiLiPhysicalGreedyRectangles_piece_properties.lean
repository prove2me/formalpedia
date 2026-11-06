-- Prove2me | solution 1 for QEC.Locality.daiLiPhysicalGreedyRectangles_piece_properties
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:07:31.457248+00:00
-- url     : https://prove2.me/submissions/1b8d938d-b480-494b-adfd-71028042c029

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Theorems.Thm_QEC_Locality_daiLiPhysicalGreedySubdivision_group_min_height
import Theorems.Thm_QEC_Locality_daiLiPhysicalGreedySubdivision_group_alternative

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
    (embedding : UnitSeparatedEmbedding2D ι) (threshold left right ell : ℝ)
    {lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hEll : 0 < ell)
    (hAtoms : DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding)
      ell lower upper atoms)
    (d : Nat) (rectangle : (ℝ × ℝ) × (ℝ × ℝ))
    (hRectangle : rectangle ∈ daiLiPhysicalGreedyRectangles
      P embedding threshold left right d atoms) :
    5 * ell ≤ rectangle.2.2 - rectangle.1.2 ∧
      (10 * regionInteractionCounter P embedding threshold
          (embedding.qubitsInRectangle rectangle.1 rectangle.2) ≤ d ∨
        rectangle.2.2 - rectangle.1.2 ≤ 10 * ell) := by
  rcases List.mem_map.mp hRectangle with ⟨piece, hPiece, rfl⟩
  constructor
  · exact daiLiPhysicalGreedySubdivision_group_min_height
      P embedding threshold left right ell hEll hAtoms d hPiece
  · exact daiLiPhysicalGreedySubdivision_group_alternative
      P embedding threshold left right ell hEll hAtoms d hPiece
end QEC.Locality
