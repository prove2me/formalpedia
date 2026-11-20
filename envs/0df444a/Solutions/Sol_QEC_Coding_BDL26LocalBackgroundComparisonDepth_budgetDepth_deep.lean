-- Prove2me | solution 1 for QEC.Coding.BDL26LocalBackgroundComparisonDepth.budgetDepth_deep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T14:37:44.859106+00:00
-- url     : https://prove2.me/submissions/12aa8258-0a12-4112-8d1b-152efc36ae9e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonResponse
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_UniformReadoutWeight
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonDepth
import Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonDepth_budgetDepth_rx_count
section
noncomputable section
namespace QEC.Coding.BDL26LocalBackgroundComparisonDepth
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual BDL26RZMap1CoordinateBridge
open BDL26LocalBackgroundComparisonResponse
open scoped Classical BigOperators
private theorem nat_lt_two_pow (k : Nat) : k < 2^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      rw [pow_succ]
      have positive : 0 < 2^k := pow_pos (by decide) _
      omega
end QEC.Coding.BDL26LocalBackgroundComparisonDepth
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalBackgroundComparisonDepth
open MultiscaleDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26IndexedDecoder BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping BDL26HistoryLogicalResidual BDL26RZMap1CoordinateBridge
open BDL26LocalBackgroundComparisonResponse
open scoped Classical BigOperators
namespace QEC.Coding.BDL26LocalBackgroundComparisonDepth
theorem _root_.solution (B : Nat) : 4*B < 2 ^ ((budgetDepth B+1)/2) := by
  rw [budgetDepth_rx_count]
  have h := nat_lt_two_pow (4*B+1)
  omega
end QEC.Coding.BDL26LocalBackgroundComparisonDepth
