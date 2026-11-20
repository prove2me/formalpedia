-- Prove2me | solution 1 for QEC.Coding.BDL26NonzeroBackgroundComparisonStability.threshold_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:40:41.998997+00:00
-- url     : https://prove2.me/submissions/b7b309a0-63df-4d4a-80e1-7e317508473b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AllDepthBottomComparisonStability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NonzeroBackgroundComparisonStability
import Theorems.Thm_QEC_Coding_BDL26FiniteTannerSquare_OddScale_two_half_add_one
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta0
import Theorems.Thm_QEC_Coding_BDL26HistoryLogicalResidual_suffix_delta1


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NonzeroBackgroundComparisonStability
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26HistoryLogicalResidual (suffix_delta0 suffix_delta1)
open BDL26RZMap1CoordinateBridge
open scoped Classical BigOperators
namespace QEC.Coding.BDL26NonzeroBackgroundComparisonStability
theorem _root_.solution (S : OddScale) (B : Nat) :
    14*B+16 ≤ S.half ↔ 28*B+33 ≤ S.ell := by
  have h := S.two_half_add_one
  omega
end QEC.Coding.BDL26NonzeroBackgroundComparisonStability
