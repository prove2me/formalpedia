-- Prove2me | solution 1 for QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse.failure_occupied_nonempty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T15:56:18.309557+00:00
-- url     : https://prove2.me/submissions/282aa5ea-350d-4621-add9-5a0439c7a6fa

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonDepth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonQueryResponse
import Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonQueryResponse_failure_occupied_card
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
theorem _root_.solution (large : 33 ≤ S.ell) (g : W S n) (q : Q S n)
    (bad : BDL26AllDepthBottomComparisonStability.residual S n
      (perturbTop S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n) g)
      (canonicalBasisWord (F:=BDL26Field) q) ∉ boundaries S n) :
    (occupiedQueries S n (BDL26NonzeroBackgroundComparisonStability.zeroInput S n)
      g (canonicalBasisWord (F:=BDL26Field) q)).Nonempty := by
  apply Finset.card_pos.mp
  exact failure_occupied_card S n 0 large (by positivity) g q bad
end QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse
