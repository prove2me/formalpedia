-- Prove2me | solution 1 for QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse.basis_syndrome_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:40:38.619615+00:00
-- url     : https://prove2.me/submissions/4565e1ef-374c-49ba-ba13-78cb2e3632d2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonDepth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonQueryResponse
import Theorems.Thm_QEC_Coding_BDL26BoundedValence_state_boundedValence
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta1
import Theorems.Thm_QEC_Coding_BDL26UniformHistoryObstruction_basis_coboundary_weight


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
theorem _root_.solution (q : Q S n) :
    HammingWeight ((SuffixData S n).family.coboundary1 (TopIndex n)
      (canonicalBasisWord (F:=BDL26Field) q)) ≤ 4 := by
  rw [suffix_delta1,BDL26UniformHistoryObstruction.basis_coboundary_weight]
  exact ((BDL26BoundedValence.state_boundedValence S (n+2)).2.2 q).2.1
end QEC.Coding.BDL26LocalBackgroundComparisonQueryResponse
