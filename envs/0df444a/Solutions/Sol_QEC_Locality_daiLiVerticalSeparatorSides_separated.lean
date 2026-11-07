-- Prove2me | solution 1 for QEC.Locality.daiLiVerticalSeparatorSides_separated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:28:59.802211+00:00
-- url     : https://prove2.me/submissions/63daf8a3-ada6-472d-9c55-268a49bec447

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
    {lowerCut upperCut threshold : ℝ} (hWidth : threshold ≤ upperCut - lowerCut)
    {p q : ι}
    (hp : p ∈ daiLiVerticalSeparatorLower embedding region lowerCut)
    (hq : q ∈ daiLiVerticalSeparatorUpper embedding region upperCut) :
    threshold ≤ embedding.distance p q := by
  have hpBelow := (Finset.mem_filter.mp hp).2
  have hqAbove := (Finset.mem_filter.mp hq).2
  rw [UnitSeparatedEmbedding2D.distance, euclideanDistance2D]
  have hSq : ((embedding.point p).1 - (embedding.point q).1) ^ 2 ≤
      ((embedding.point p).1 - (embedding.point q).1) ^ 2 +
        ((embedding.point p).2 - (embedding.point q).2) ^ 2 := by
    nlinarith [sq_nonneg ((embedding.point p).2 - (embedding.point q).2)]
  have hCoordinate : upperCut - lowerCut ≤
      (embedding.point q).1 - (embedding.point p).1 := by
    linarith
  calc
    threshold ≤ upperCut - lowerCut := hWidth
    _ ≤ (embedding.point q).1 - (embedding.point p).1 := hCoordinate
    _ ≤ |(embedding.point p).1 - (embedding.point q).1| := by
      rw [abs_sub_comm]
      exact le_abs_self _
    _ ≤ _ := Real.abs_le_sqrt hSq
end QEC.Locality
