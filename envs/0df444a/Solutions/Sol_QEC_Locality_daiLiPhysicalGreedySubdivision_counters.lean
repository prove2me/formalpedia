-- Prove2me | solution 1 for QEC.Locality.daiLiPhysicalGreedySubdivision_counters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:38:48.82478+00:00
-- url     : https://prove2.me/submissions/c5f8a16f-9f34-41db-aa53-caaa1d1e37d3

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Theorems.Thm_QEC_Locality_daiLiGreedyScanWith_map

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
    (daiLiPhysicalGreedySubdivision P embedding threshold left right d atoms).map
        (daiLiAtomCounters P embedding threshold left right) =
      daiLiGreedyAtomicSubdivision d
        (daiLiAtomCounters P embedding threshold left right atoms) := by
  exact daiLiGreedyScanWith_map
        (fun atom => regionInteractionCounter P embedding threshold
          (daiLiAtomQubits embedding left right atom)) d atoms [] []
end QEC.Locality
