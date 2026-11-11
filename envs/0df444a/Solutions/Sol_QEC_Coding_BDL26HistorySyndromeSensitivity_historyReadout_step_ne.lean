-- Prove2me | solution 1 for QEC.Coding.BDL26HistorySyndromeSensitivity.historyReadout_step_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:51:40.521054+00:00
-- url     : https://prove2.me/submissions/85f80533-5907-4688-8563-d3ff7c899276

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Steps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_CanonicalHistoryMarks_Snapshots
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_historyReadout_cons

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical
universe u
variable {depth : Nat} {C0 C1 C2 : LevelIndex depth → Type u}
variable [∀ i, Fintype (C0 i)] [∀ i, Fintype (C1 i)] [∀ i, Fintype (C2 i)]
namespace QEC.Coding.BDL26HistorySyndromeSensitivity
theorem _root_.solution (D : BDL26DecoderData depth C0 C1 C2)
    (i : StepIndex depth) (out : AssemblyStepOutput D i) (H : CorrectionHistory D)
    (a : LevelIndex depth) (ha : i.succ ≠ a) :
    historyInputReadout D (.step i out :: H) a = historyInputReadout D H a := by
  rw [historyReadout_cons]
  change (if h : i.succ = a then h ▸ out.input.val else 0) + _ = _
  split_ifs with h
  · exact False.elim (ha h)
  · exact zero_add _
end QEC.Coding.BDL26HistorySyndromeSensitivity
