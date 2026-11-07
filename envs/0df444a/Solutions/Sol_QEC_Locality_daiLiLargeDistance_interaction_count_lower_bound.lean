-- Prove2me | solution 1 for QEC.Locality.daiLiLargeDistance_interaction_count_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:48:11.434348+00:00
-- url     : https://prove2.me/submissions/e91d255f-1f09-4342-bab3-ff1964843360

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Locality_OptimalTradeoff_LargeDistanceSeparator
import Theorems.Thm_QEC_Locality_daiLiLargeDistance_fewLongInteractions_encodedQubits_eq_zero

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
    (hDistance : StabilizerCode.SemanticStabilizerDistance P.code d)
    (hAboveBPT : 100 * Fintype.card ι ≤ P.encodedQubits * d ^ 2)
    (hLargeDistance : Real.sqrt ((P.encodedQubits : ℝ) * (Fintype.card ι : ℝ)) ≤ d)
    (hEncodedPositive : 0 < P.encodedQubits) :
    d ≤ 200 * P.longInteractionCount embedding
      (daiLiLargeDistanceThreshold d (Fintype.card ι)) := by
  by_contra hCount
  have hFew : DaiLiLargeDistanceFewLongInteractions P embedding d := by
    unfold DaiLiLargeDistanceFewLongInteractions
    omega
  have hZero := daiLiLargeDistance_fewLongInteractions_encodedQubits_eq_zero
    P embedding d hDistance hAboveBPT hLargeDistance hFew
  omega
end QEC.Locality
