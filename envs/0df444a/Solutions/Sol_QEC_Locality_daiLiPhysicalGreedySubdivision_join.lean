-- Prove2me | solution 1 for QEC.Locality.daiLiPhysicalGreedySubdivision_join
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:54:53.076074+00:00
-- url     : https://prove2.me/submissions/2740ad0e-9935-4dd4-8aab-e8d9777cffb7

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Theorems.Thm_QEC_Locality_daiLiGreedySubdivisionWith_join

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
    (d : Nat) (atoms : List (ℝ × ℝ)) :
    (daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms).flatten = atoms := by
  exact daiLiGreedySubdivisionWith_join
    (fun atom => regionInteractionCounter P embedding threshold
      (daiLiAtomQubits embedding left right atom)) d atoms
end QEC.Locality
