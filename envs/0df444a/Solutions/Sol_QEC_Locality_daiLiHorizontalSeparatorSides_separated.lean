-- Prove2me | solution 1 for QEC.Locality.daiLiHorizontalSeparatorSides_separated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:28:19.834814+00:00
-- url     : https://prove2.me/submissions/38be7eae-8fa1-4cdf-849b-069f4d017a68

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Locality_OptimalTradeoff_LargeDistanceSeparator
section
noncomputable section
namespace QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
omit [Fintype ι] [DecidableEq ι] in
/-- A lower bound on a vertical coordinate difference gives the same lower
bound on the stored Euclidean distance.  This local version is kept here
because the Part-I selector must not depend on the later grid partition. -/
private theorem daiLi_le_distance_of_le_abs_vertical_coordinate
    (embedding : UnitSeparatedEmbedding2D ι) {p q : ι} {r : ℝ}
    (h : r ≤ |(embedding.point p).2 - (embedding.point q).2|) :
    r ≤ embedding.distance p q := by
  rw [UnitSeparatedEmbedding2D.distance, euclideanDistance2D]
  have hSq : ((embedding.point p).2 - (embedding.point q).2) ^ 2 ≤
      ((embedding.point p).1 - (embedding.point q).1) ^ 2 +
        ((embedding.point p).2 - (embedding.point q).2) ^ 2 := by
    nlinarith [sq_nonneg ((embedding.point p).1 - (embedding.point q).1)]
  exact h.trans (Real.abs_le_sqrt hSq)
end QEC.Locality
end
end

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
    (hp : p ∈ daiLiHorizontalSeparatorLower embedding region lowerCut)
    (hq : q ∈ daiLiHorizontalSeparatorUpper embedding region upperCut) :
    threshold ≤ embedding.distance p q := by
  have hpBelow := (Finset.mem_filter.mp hp).2
  have hqAbove := (Finset.mem_filter.mp hq).2
  apply daiLi_le_distance_of_le_abs_vertical_coordinate embedding
  rw [le_abs]
  right
  linarith
end QEC.Locality
