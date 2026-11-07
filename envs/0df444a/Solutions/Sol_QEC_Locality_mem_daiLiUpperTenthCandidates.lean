-- Prove2me | solution 1 for QEC.Locality.mem_daiLiUpperTenthCandidates
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:25:37.010664+00:00
-- url     : https://prove2.me/submissions/95bb00c7-21c6-4600-98be-2236fcc5d35c

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
    daiLiUpperTenthCoordinate region coordinate hRegion ∈
      daiLiUpperTenthCandidates region coordinate := by
  unfold daiLiUpperTenthCoordinate
  exact Finset.max'_mem _ _
end QEC.Locality
