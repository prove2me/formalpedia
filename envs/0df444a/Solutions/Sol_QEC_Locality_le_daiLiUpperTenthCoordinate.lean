-- Prove2me | solution 1 for QEC.Locality.le_daiLiUpperTenthCoordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:25:45.513501+00:00
-- url     : https://prove2.me/submissions/c0d27c65-3d23-4f08-b6ee-3a4e6479c26f

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
    {candidate : ℝ} (hCandidate : candidate ∈ daiLiUpperTenthCandidates region coordinate) :
    candidate ≤ daiLiUpperTenthCoordinate region coordinate hRegion := by
  unfold daiLiUpperTenthCoordinate
  exact Finset.le_max' _ _ hCandidate
end QEC.Locality
