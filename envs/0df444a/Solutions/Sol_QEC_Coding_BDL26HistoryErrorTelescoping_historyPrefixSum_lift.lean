-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.historyPrefixSum_lift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:41:36.511647+00:00
-- url     : https://prove2.me/submissions/bcb11c5c-399b-4a3e-a6c5-4b07b2c3ce92

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_historyPrefixSum_split
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_historyIntervalSum_zero_of_levels

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open BDL26DecodingGraph
open scoped Classical
universe u v
variable {depth : Nat} {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
namespace QEC.Coding.BDL26HistoryErrorTelescoping
theorem _root_.solution (D : BDL26DecoderData depth C0 C1 C2)
    (H : CorrectionHistory D) (a b : LevelIndex depth) (hab : a.val ≤ b.val)
    (h : ∀ e ∈ H, e.level ≤ a.val) :
    historyPrefixSum D H b = intervalMap1 D a b hab (historyPrefixSum D H a) := by
  have hs := historyPrefixSum_split D H a b hab
  rw [historyIntervalSum_zero_of_levels D H a b h,zero_add] at hs
  exact hs
end QEC.Coding.BDL26HistoryErrorTelescoping
