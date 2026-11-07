-- Prove2me | solution 1 for QEC.Locality.card_daiLiTenthExterior_le_four_mul_tenth_pred
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:30:15.485758+00:00
-- url     : https://prove2.me/submissions/8351c21b-2469-4e36-8e1d-fdca294ac0b4

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Locality_OptimalTradeoff_LargeDistanceSeparator
import Theorems.Thm_QEC_Locality_card_coordinate_lt_daiLiLowerTenthCoordinate_lt_tenth
import Theorems.Thm_QEC_Locality_card_daiLiUpperTenthCoordinate_lt_coordinate_lt_tenth

set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
omit [Fintype ι]
namespace QEC.Locality
theorem _root_.solution
    (embedding : UnitSeparatedEmbedding2D ι) (region : Finset ι)
    (hRegion : region.Nonempty) :
    (daiLiTenthExterior embedding region hRegion).card ≤
      4 * (daiLiTenthCount region - 1) := by
  classical
  have hXLower := card_coordinate_lt_daiLiLowerTenthCoordinate_lt_tenth
    region (fun p => (embedding.point p).1) hRegion
  have hXUpper := card_daiLiUpperTenthCoordinate_lt_coordinate_lt_tenth
    region (fun p => (embedding.point p).1) hRegion
  have hYLower := card_coordinate_lt_daiLiLowerTenthCoordinate_lt_tenth
    region (fun p => (embedding.point p).2) hRegion
  have hYUpper := card_daiLiUpperTenthCoordinate_lt_coordinate_lt_tenth
    region (fun p => (embedding.point p).2) hRegion
  unfold daiLiTenthExterior
  calc
    _ ≤ ((region.filter fun q => (embedding.point q).1 <
          daiLiLowerTenthCoordinate region (fun p => (embedding.point p).1) hRegion) ∪
        (region.filter fun q =>
          daiLiUpperTenthCoordinate region (fun p => (embedding.point p).1) hRegion <
            (embedding.point q).1) ∪
        (region.filter fun q => (embedding.point q).2 <
          daiLiLowerTenthCoordinate region (fun p => (embedding.point p).2) hRegion)).card +
        (region.filter fun q =>
          daiLiUpperTenthCoordinate region (fun p => (embedding.point p).2) hRegion <
            (embedding.point q).2).card := Finset.card_union_le _ _
    _ ≤ (((region.filter fun q => (embedding.point q).1 <
          daiLiLowerTenthCoordinate region (fun p => (embedding.point p).1) hRegion) ∪
        (region.filter fun q =>
          daiLiUpperTenthCoordinate region (fun p => (embedding.point p).1) hRegion <
            (embedding.point q).1)).card +
        (region.filter fun q => (embedding.point q).2 <
          daiLiLowerTenthCoordinate region (fun p => (embedding.point p).2) hRegion).card) +
        (region.filter fun q =>
          daiLiUpperTenthCoordinate region (fun p => (embedding.point p).2) hRegion <
            (embedding.point q).2).card := by
      exact Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ (((region.filter fun q => (embedding.point q).1 <
          daiLiLowerTenthCoordinate region (fun p => (embedding.point p).1) hRegion).card +
        (region.filter fun q =>
          daiLiUpperTenthCoordinate region (fun p => (embedding.point p).1) hRegion <
            (embedding.point q).1).card) +
        (region.filter fun q => (embedding.point q).2 <
          daiLiLowerTenthCoordinate region (fun p => (embedding.point p).2) hRegion).card) +
        (region.filter fun q =>
          daiLiUpperTenthCoordinate region (fun p => (embedding.point p).2) hRegion <
            (embedding.point q).2).card := by
      exact Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _
    _ ≤ 4 * (daiLiTenthCount region - 1) := by omega
end QEC.Locality
