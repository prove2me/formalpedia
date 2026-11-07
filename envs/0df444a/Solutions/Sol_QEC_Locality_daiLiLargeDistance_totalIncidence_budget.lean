-- Prove2me | solution 1 for QEC.Locality.daiLiLargeDistance_totalIncidence_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T13:03:55.525207+00:00
-- url     : https://prove2.me/submissions/27f4d5a0-4bd1-4ca1-988f-5a1026df928b

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Locality_OptimalTradeoff_LargeDistanceSeparator
import Theorems.Thm_QEC_Coding_StabilizerCode_BinaryStabilizerPresentation_sum_daiLiInteractionCounter_eq_two_mul_longInteractionCount


set_option autoImplicit false
noncomputable section
open QEC QEC.Locality
open QEC Semantics Coding PauliSymplectic
open Coding.StabilizerCode
open Coding.StabilizerCode.BinaryStabilizerPresentation
universe u v
variable {ι : Type u} [Fintype ι] [DecidableEq ι]
variable {κ : Type v} [Fintype κ]
namespace QEC.Locality
theorem _root_.solution
    (P : BinaryStabilizerPresentation (ι := ι) (κ := κ))
    (embedding : UnitSeparatedEmbedding2D ι) (d : Nat)
    (hFew : DaiLiLargeDistanceFewLongInteractions P embedding d) :
    10 * (∑ q : ι,
      P.daiLiInteractionCounter embedding
        (daiLiLargeDistanceThreshold d (Fintype.card ι)) q) ≤ d := by
  unfold DaiLiLargeDistanceFewLongInteractions at hFew
  rw [P.sum_daiLiInteractionCounter_eq_two_mul_longInteractionCount embedding
    (daiLiLargeDistanceThreshold d (Fintype.card ι))]
  omega
end QEC.Locality
