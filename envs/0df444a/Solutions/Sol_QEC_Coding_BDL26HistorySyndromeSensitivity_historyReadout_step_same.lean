-- Prove2me | solution 1 for QEC.Coding.BDL26HistorySyndromeSensitivity.historyReadout_step_same
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:51:30.174213+00:00
-- url     : https://prove2.me/submissions/4581085c-b14c-4a23-87b5-b24abecbfc2c

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
    (i : StepIndex depth) (out : AssemblyStepOutput D i) (H : CorrectionHistory D) :
    historyInputReadout D (.step i out :: H) i.succ =
      out.input.val + historyInputReadout D H i.succ := by
  rw [historyReadout_cons]
  change (if h : i.succ = i.succ then h ▸ out.input.val else 0) + _ = _
  rw [dif_pos rfl]
end QEC.Coding.BDL26HistorySyndromeSensitivity
