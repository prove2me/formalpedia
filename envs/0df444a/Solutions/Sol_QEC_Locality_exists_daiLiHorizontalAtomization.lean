-- Prove2me | solution 1 for QEC.Locality.exists_daiLiHorizontalAtomization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:51:13.259532+00:00
-- url     : https://prove2.me/submissions/c18b0dda-a6b4-4ac5-94d9-0ec7c8909312

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Theorems.Thm_QEC_Locality_exists_daiLiHorizontalAtomization_of_budget

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
    (support : Finset ℝ) (ell lower upper : ℝ) (hEll : 0 < ell)
    (hMin : 5 * ell ≤ upper - lower) :
    ∃ atoms, DaiLiHorizontalAtomization support ell lower upper atoms := by
  have hScale : 0 < 5 * ell := by linarith
  obtain ⟨budget, hBudget⟩ := exists_nat_gt ((upper - lower) / (5 * ell))
  have hBound : upper - lower ≤ 20 * ell + (budget : ℝ) * (5 * ell) := by
    have hStrict : upper - lower < (budget : ℝ) * (5 * ell) :=
      (div_lt_iff₀ hScale).mp hBudget
    linarith
  exact exists_daiLiHorizontalAtomization_of_budget support ell hEll budget lower upper hMin hBound
end QEC.Locality
