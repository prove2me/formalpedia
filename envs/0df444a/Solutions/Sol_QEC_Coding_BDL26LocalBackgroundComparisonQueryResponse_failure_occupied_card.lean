-- Prove2me | solution 1 for QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse.failure_occupied_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T15:48:01.564917+00:00
-- url     : https://prove2.me/submissions/0c67ed5f-6bcb-4339-8b8b-0935b75ff7d3

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonDepth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonQueryResponse
import Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonQueryResponse_restriction_support
import Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonQueryResponse_failure_occupied_weight
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta1


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
    B < (occupiedQueries S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n)
      g (canonicalBasisWord (F:=BDL26Field) q)).card := by
  have h := failure_occupied_weight S n B large deep g q bad
  rwa [HammingWeight_eq_card_hammingSupport,restriction_support] at h
end QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse
