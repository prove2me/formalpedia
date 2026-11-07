-- Prove2me | solution 1 for QEC.Locality.daiLiLowerTenthCoordinate_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:25:34.36105+00:00
-- url     : https://prove2.me/submissions/5d860665-48b7-4932-aab5-442a4b2c3563

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
    (region : Finset ι) (coordinate : ι → ℝ) (hRegion : region.Nonempty)
    {candidate : ℝ} (hCandidate : candidate ∈ daiLiLowerTenthCandidates region coordinate) :
    daiLiLowerTenthCoordinate region coordinate hRegion ≤ candidate := by
  unfold daiLiLowerTenthCoordinate
  exact Finset.min'_le _ _ hCandidate
end QEC.Locality
