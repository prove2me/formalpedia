-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.historyIntervalSum_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:29:59.260456+00:00
-- url     : https://prove2.me/submissions/739bd210-918a-4f2c-bc0c-ddebf6a1cb73

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_sum


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
    (H : CorrectionHistory D) (a : LevelIndex depth) : historyIntervalSum D H a a = 0 := by
  have hnone : ∀ e : CorrectionHistoryEntry D, intervalEntry D a a e = none := by
    intro e
    cases e with
    | base B => rfl
    | step i O =>
        have h : ¬ (a.val < i.succ.val ∧ i.succ.val ≤ a.val) := by omega
        exact dif_neg h
  induction H with
  | nil => rfl
  | cons e H ih =>
      change ((e :: H).filterMap (intervalEntry D a a)).sum = 0
      rw [List.filterMap_cons,hnone e]
      exact ih
end QEC.Coding.BDL26HistoryErrorTelescoping
