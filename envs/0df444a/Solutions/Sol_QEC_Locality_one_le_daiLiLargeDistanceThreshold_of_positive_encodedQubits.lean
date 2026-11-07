-- Prove2me | solution 1 for QEC.Locality.one_le_daiLiLargeDistanceThreshold_of_positive_encodedQubits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:33:59.325515+00:00
-- url     : https://prove2.me/submissions/60428fea-fd15-4e38-b4b2-f506ff55a8db

import Definitions.Def_QEC_Locality_OptimalTradeoff_RecursivePartition
import Definitions.Def_QEC_Locality_OptimalTradeoff_BadSquareSubdivision
import Definitions.Def_QEC_Locality_CorrectableRegions_TwoCorrectableRegionsDimension
import Definitions.Def_QEC_Locality_OptimalTradeoff_LargeDistanceSeparator
import Theorems.Thm_QEC_Locality_daiLiLargeDistance_threshold_lt_one_encodedQubits_eq_zero

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
    (hFew : DaiLiLargeDistanceFewLongInteractions P embedding d)
    (hdTwo : 2 ≤ d) (hEncoded : 0 < P.encodedQubits) :
    1 ≤ daiLiLargeDistanceThreshold d (Fintype.card ι) := by
  by_contra hThreshold
  have hZero := daiLiLargeDistance_threshold_lt_one_encodedQubits_eq_zero
    P embedding d hDistance hFew hdTwo (lt_of_not_ge hThreshold)
  omega
end QEC.Locality
