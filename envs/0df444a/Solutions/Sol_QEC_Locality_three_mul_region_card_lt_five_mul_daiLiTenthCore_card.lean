-- Prove2me | solution 1 for QEC.Locality.three_mul_region_card_lt_five_mul_daiLiTenthCore_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:36:09.861234+00:00
-- url     : https://prove2.me/submissions/f371f243-dfc4-49a4-a884-62f3c63daf30

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Locality_OptimalTradeoff_LargeDistanceSeparator
import Theorems.Thm_QEC_Locality_six_tenths_region_card_lt_daiLiTenthCore_card

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
    3 * region.card < 5 * (daiLiTenthCore embedding region hRegion).card := by
  have hCore := six_tenths_region_card_lt_daiLiTenthCore_card embedding region hRegion hTen
  omega
end QEC.Locality
