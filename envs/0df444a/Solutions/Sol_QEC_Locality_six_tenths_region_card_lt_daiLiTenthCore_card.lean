-- Prove2me | solution 1 for QEC.Locality.six_tenths_region_card_lt_daiLiTenthCore_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:33:52.229159+00:00
-- url     : https://prove2.me/submissions/800aa898-f90e-4647-af20-52c15a42785e

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Locality_OptimalTradeoff_LargeDistanceSeparator
import Theorems.Thm_QEC_Locality_daiLiTenthCore_complement_subset_exterior
import Theorems.Thm_QEC_Locality_card_daiLiTenthExterior_le_four_mul_tenth_pred

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
    (hRegion : region.Nonempty) (hTen : 10 ≤ region.card) :
    6 * region.card / 10 < (daiLiTenthCore embedding region hRegion).card := by
  classical
  have hCoreSubset : daiLiTenthCore embedding region hRegion ⊆ region :=
    Finset.filter_subset _ _
  have hComplement := daiLiTenthCore_complement_subset_exterior embedding region hRegion
  have hExterior := card_daiLiTenthExterior_le_four_mul_tenth_pred embedding region hRegion
  have hComplementCard : (region \ daiLiTenthCore embedding region hRegion).card ≤
      4 * (daiLiTenthCount region - 1) :=
    (Finset.card_le_card hComplement).trans hExterior
  have hSplit := Finset.card_sdiff_add_card_eq_card hCoreSubset
  unfold daiLiTenthCount at hComplementCard
  omega
end QEC.Locality
