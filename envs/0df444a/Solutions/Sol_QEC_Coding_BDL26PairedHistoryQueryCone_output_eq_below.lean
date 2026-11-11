-- Prove2me | solution 1 for QEC.Coding.BDL26PairedHistoryQueryCone.output_eq_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:32:25.96344+00:00
-- url     : https://prove2.me/submissions/4ece153f-c827-41cb-8293-075b71577dbc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_ReadBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone
import Theorems.Thm_QEC_Coding_BDL26PairedHistoryQueryCone_inputs_eq_below

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedHistoryQueryCone
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26PairedHistoryQueryCone
theorem _root_.solution (s t : TopInput S n) (a : LevelIndex n)
    (hs : actualInputs S n s a = actualInputs S n t a)
    (i : StepIndex n) (hi : i.succ.val ≤ a.val) :
    actualOutput S n s i = actualOutput S n t i := by
  unfold actualOutput
  rw [inputs_eq_below S n s t a i.succ hi hs]
end QEC.Coding.BDL26PairedHistoryQueryCone
