-- Prove2me | solution 1 for QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse.failure_occupied_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T15:31:20.228948+00:00
-- url     : https://prove2.me/submissions/55a35974-061c-4153-8c0c-097c69348ccd

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonDepth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonQueryResponse
import Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonQueryResponse_nonboundary_restriction
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta1
import Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonDepth_fixed_scale_small_background_stable


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26RZMap1CoordinateBridge
open BDL26HistoryLogicalResidual (suffix_delta1)
open BDL26LocalBackgroundComparisonResponse BDL26PairedHistoryQueryCone
open MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse
theorem _root_.solution (B : Nat) (large : 33 ≤ S.ell)
    (deep : 4*B < 2^((n+1)/2)) (g : W S n) (q : Q S n)
    (bad : BDL26AllDepthBottomComparisonStability.residual S n
      (perturbTop S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n) g)
      (canonicalBasisWord (F:=BDL26Field) q) ∉ boundaries S n) :
    B < HammingWeight (backgroundRestriction S n g
      (queryMask S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n) g
        (canonicalBasisWord (F:=BDL26Field) q))) := by
  by_contra hn
  have hsmall : HammingWeight (backgroundRestriction S n g
      (queryMask S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n) g
        (canonicalBasisWord (F:=BDL26Field) q))) ≤ B := by omega
  exact nonboundary_restriction S n _ g q bad
    (BDL26LocalBackgroundComparisonDepth.fixed_scale_small_background_stable S n B large deep
      _ hsmall q)
end QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse
