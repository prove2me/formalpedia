-- Prove2me | solution 1 for QEC.Locality.DaiLiHorizontalAtomization.minimum_height
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:50:18.226746+00:00
-- url     : https://prove2.me/submissions/9f693efa-a338-4ef3-8eff-bcf5a391ca66

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Theorems.Thm_QEC_Locality_DaiLiHorizontalAtomization_lower_lt_upper

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ]
namespace QEC.Locality
namespace DaiLiHorizontalAtomization
theorem _root_.solution
    {support : Finset ℝ} {ell lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization support ell lower upper atoms)
    (hEll : 0 < ell) :
    5 * ell ≤ upper - lower := by
  induction hAtoms with
  | single hHeight => exact hHeight.1
  | @cons lower cut upper tail hCutFree hHeight hTail ih =>
      have hTailPositive : cut < upper := hTail.lower_lt_upper hEll
      exact hHeight.1.trans (by linarith)
end DaiLiHorizontalAtomization
end QEC.Locality
