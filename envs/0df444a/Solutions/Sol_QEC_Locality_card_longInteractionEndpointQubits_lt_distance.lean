-- Prove2me | solution 1 for QEC.Locality.card_longInteractionEndpointQubits_lt_distance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:24:54.378994+00:00
-- url     : https://prove2.me/submissions/3d7189f6-0cd8-4b4e-950f-3ee4ca7c23a5

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Locality_OptimalTradeoff_LargeDistanceSeparator
import Theorems.Thm_QEC_Locality_daiLiLargeDistance_totalIncidence_budget
import Theorems.Thm_QEC_Locality_card_longInteractionEndpointQubits_le_sum_counter


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
    (hFew : DaiLiLargeDistanceFewLongInteractions P embedding d) (hd : 0 < d) :
    (longInteractionEndpointQubits P embedding
      (daiLiLargeDistanceThreshold d (Fintype.card ι))).card < d := by
  have hEndpoints := card_longInteractionEndpointQubits_le_sum_counter P embedding
    (daiLiLargeDistanceThreshold d (Fintype.card ι))
  have hBudget := daiLiLargeDistance_totalIncidence_budget P embedding d hFew
  have hEndpointBudget :
      10 * (longInteractionEndpointQubits P embedding
        (daiLiLargeDistanceThreshold d (Fintype.card ι))).card ≤ d :=
    (Nat.mul_le_mul_left 10 hEndpoints).trans hBudget
  omega
end QEC.Locality
