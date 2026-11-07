-- Prove2me | solution 1 for QEC.Locality.daiLiHorizontalSeparatorLower_disjoint_upper
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:27:57.346987+00:00
-- url     : https://prove2.me/submissions/ae43dab9-b59b-4c15-bfe1-a43fc7d4fcb6

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Locality_OptimalTradeoff_LargeDistanceSeparator

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
omit [Fintype ι] [DecidableEq ι]
namespace QEC.Locality
theorem _root_.solution
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    {lowerCut upperCut : ℝ} (hCuts : lowerCut ≤ upperCut) :
    Disjoint (daiLiHorizontalSeparatorLower embedding region lowerCut)
      (daiLiHorizontalSeparatorUpper embedding region upperCut) := by
  apply Finset.disjoint_left.mpr
  intro q hLower hUpper
  have hBelow := (Finset.mem_filter.mp hLower).2
  have hAbove := (Finset.mem_filter.mp hUpper).2
  linarith
end QEC.Locality
