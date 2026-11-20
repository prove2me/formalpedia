-- Prove2me | solution 1 for QEC.Coding.BDL26NonzeroBackgroundComparisonStability.scaleSixtyOne_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:25:04.235557+00:00
-- url     : https://prove2.me/submissions/a8e88f2d-75c3-47e5-af8f-cb695cf9452c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_AllDepthBottomComparisonStability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NonzeroBackgroundComparisonStability
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
theorem _root_.solution : scaleSixtyOne.half=30 := by decide
end QEC.Coding.BDL26NonzeroBackgroundComparisonStability
