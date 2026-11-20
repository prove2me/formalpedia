-- Prove2me | solution 1 for QEC.Coding.BDL26LocalBackgroundComparisonDepth.budgetDepth_source_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:31:17.213877+00:00
-- url     : https://prove2.me/submissions/568e84e5-154e-490c-8246-b5c82e451b52

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
theorem _root_.solution (B : Nat) :
    budgetDepth B+2=2*(4*B+2) ∧ 0 < budgetDepth B := by
  unfold budgetDepth
  omega
end QEC.Coding.BDL26LocalBackgroundComparisonDepth
