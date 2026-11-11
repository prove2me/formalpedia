-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.historyThrough_levels
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:30:58.388217+00:00
-- url     : https://prove2.me/submissions/fe236f5f-91bc-4141-9a11-bf8201bb266f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_Intervals
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums

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
    (H : CorrectionHistory D) (b : LevelIndex depth) :
    ∀ e ∈ historyThrough D H b, e.level ≤ b.val := by
  intro e he
  have h := (List.mem_filter.mp he).2
  exact of_decide_eq_true h
end QEC.Coding.BDL26HistoryErrorTelescoping
