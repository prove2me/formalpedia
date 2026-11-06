-- Prove2me | solution 1 for QEC.Locality.exists_real_in_openInterval_not_mem_finset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:58:08.104046+00:00
-- url     : https://prove2.me/submissions/a02f6f42-06dd-43f4-95b4-1a94b5477a0f

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
namespace QEC.Locality
theorem _root_.solution
    (support : Finset ℝ) {lower upper : ℝ} (hInterval : lower < upper) :
    ∃ cut : ℝ, lower < cut ∧ cut < upper ∧ cut ∉ support := by
  by_contra hExists
  push Not at hExists
  have hSubset : Set.Ioo lower upper ⊆ (support : Set ℝ) := by
    intro cut hCut
    exact hExists cut hCut.1 hCut.2
  exact (Set.Ioo_infinite hInterval) (support.finite_toSet.subset hSubset)
end QEC.Locality
