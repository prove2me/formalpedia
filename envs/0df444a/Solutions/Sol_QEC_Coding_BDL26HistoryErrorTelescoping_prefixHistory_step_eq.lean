-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.prefixHistory_step_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:35:21.24551+00:00
-- url     : https://prove2.me/submissions/c2b5dcd7-c503-4b80-aad0-cfb15fb9ad89

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
    (st : AlternatingStepData D) (B : AuditedBaseDecoder D)
    (i : StepIndex depth) (s : D.family.Syndrome i.succ) :
    prefixHistory D st B (i.val+1) (Nat.succ_le_of_lt i.isLt) s =
      .step i (st.step i s) ::
        prefixHistory D st B i.val (Nat.le_of_lt i.isLt) (st.step i s).coarse := by
  rw [prefixHistory] <;> rfl
end QEC.Coding.BDL26HistoryErrorTelescoping
