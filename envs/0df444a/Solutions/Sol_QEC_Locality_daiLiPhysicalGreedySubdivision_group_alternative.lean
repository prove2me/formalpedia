-- Prove2me | solution 1 for QEC.Locality.daiLiPhysicalGreedySubdivision_group_alternative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T18:05:04.558193+00:00
-- url     : https://prove2.me/submissions/df7a0af6-feb1-467a-80bd-a49764d23749

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Theorems.Thm_QEC_Locality_daiLiPhysicalGreedySubdivision_admissible
import Theorems.Thm_QEC_Locality_daiLiPhysicalGreedySubdivision_group_short_height
import Theorems.Thm_QEC_Locality_daiLiPhysicalGreedySubdivision_group_counter

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
    {lower upper : ℝ} {atoms piece : List (ℝ × ℝ)}
    (hEll : 0 < ell)
    (hAtoms : DaiLiHorizontalAtomization (daiLiGlobalVerticalQubitSupport embedding)
      ell lower upper atoms)
    (d : Nat)
    (hPiece : piece ∈ daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms) :
    10 * regionInteractionCounter P embedding threshold
        (embedding.qubitsInRectangle
          (daiLiAtomGroupRectangle left right piece).1
          (daiLiAtomGroupRectangle left right piece).2) ≤ d ∨
      (daiLiAtomGroupRectangle left right piece).2.2 -
        (daiLiAtomGroupRectangle left right piece).1.2 ≤ 10 * ell := by
  rcases daiLiPhysicalGreedySubdivision_admissible
      P embedding threshold left right d atoms piece hPiece with
    ⟨_, hLow | hShort⟩
  · left
    rw [← daiLiPhysicalGreedySubdivision_group_counter
      P embedding threshold left right ell hEll hAtoms d hPiece]
    exact hLow
  · right
    exact daiLiPhysicalGreedySubdivision_group_short_height
      P embedding threshold left right ell hAtoms d hPiece hShort
end QEC.Locality
