-- Prove2me | solution 1 for QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse.queryMask_window_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T15:04:54.444991+00:00
-- url     : https://prove2.me/submissions/bbe7efd1-2985-419d-ad0a-4e78d9301d0c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonDepth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonQueryResponse
import Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonQueryResponse_physicalPullback_card
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta1
import Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_queries_window_card
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


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
theorem _root_.solution (sigma0 : TopInput S n) (g e : W S n)
    (L w : Nat) (hstop : 0 < (queryStop S n sigma0 g e).val)
    (hlen : n-(queryStop S n sigma0 g e).val ≤ L)
    (hw : HammingWeight ((SuffixData S n).family.coboundary1 (TopIndex n) e) ≤ w) :
    (queryMask S n sigma0 g e).card ≤ 7*windowBudget S L w := by
  exact (physicalPullback_card S n (topQueries S n sigma0 g e)).trans
    (Nat.mul_le_mul_left 7 (queries_window_card S n e _ hstop L w hw hlen))
end QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse
