-- Prove2me | solution 1 for QEC.Locality.mem_daiLiLowerTenthCandidates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:25:14.112009+00:00
-- url     : https://prove2.me/submissions/2b4b62a6-5e60-41de-8ef8-90dbe4c60e6e

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
    (region : Finset ι) (coordinate : ι → ℝ) (hRegion : region.Nonempty) :
    daiLiLowerTenthCoordinate region coordinate hRegion ∈
      daiLiLowerTenthCandidates region coordinate := by
  unfold daiLiLowerTenthCoordinate
  exact Finset.min'_mem _ _
end QEC.Locality
