-- Prove2me | solution 1 for QEC.Coding.BDL26LocalBackgroundComparisonDepth.budgetDepth_rx_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:28:54.74402+00:00
-- url     : https://prove2.me/submissions/7cb66393-f2db-4b63-a576-1938448409e1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonResponse
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonDepth

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalBackgroundComparisonDepth
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual BDL26RZMap1CoordinateBridge
open BDL26LocalBackgroundComparisonResponse
open scoped Classical BigOperators
namespace QEC.Coding.BDL26LocalBackgroundComparisonDepth
theorem _root_.solution (B : Nat) : (budgetDepth B+1)/2=4*B+1 := by
  unfold budgetDepth
  omega
end QEC.Coding.BDL26LocalBackgroundComparisonDepth
