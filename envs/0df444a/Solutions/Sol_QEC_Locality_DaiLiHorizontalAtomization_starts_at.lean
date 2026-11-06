-- Prove2me | solution 1 for QEC.Locality.DaiLiHorizontalAtomization.starts_at
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T17:04:50.551078+00:00
-- url     : https://prove2.me/submissions/cc369211-3c05-42a4-8592-f253fe4bf2be

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
    (hAtoms : DaiLiHorizontalAtomization support ell lower upper atoms) :
    ∃ firstUpper tail, atoms = (lower, firstUpper) :: tail := by
  cases hAtoms with
  | single hHeight => exact ⟨upper, [], rfl⟩
  | cons hCutFree hHeight hTail => exact ⟨_, _, rfl⟩
end DaiLiHorizontalAtomization
end QEC.Locality
