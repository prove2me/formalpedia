-- Prove2me | solution 1 for QEC.Locality.DaiLiHorizontalAtomization.lower_lt_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T16:57:28.210114+00:00
-- url     : https://prove2.me/submissions/0049f4b0-fedc-4eb5-aa76-3fd82fe2286b

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
namespace DaiLiHorizontalAtomization
theorem _root_.solution
    {support : Finset ℝ} {ell lower upper : ℝ} {atoms : List (ℝ × ℝ)}
    (hAtoms : DaiLiHorizontalAtomization support ell lower upper atoms)
    (hEll : 0 < ell) : lower < upper := by
  induction hAtoms with
  | single hHeight =>
      rcases hHeight with ⟨hLower, _⟩
      linarith
  | @cons lower cut upper tail hCutFree hHeight hTail ih =>
      rcases hHeight with ⟨hLower, _⟩
      exact (by linarith : lower < cut).trans ih
end DaiLiHorizontalAtomization
end QEC.Locality
