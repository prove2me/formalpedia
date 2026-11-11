-- Prove2me | solution 1 for QEC.Coding.BDL26PairedHistoryQueryCone.inputs_eq_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:16:57.080185+00:00
-- url     : https://prove2.me/submissions/dce982bd-397d-4083-a0f9-bb458ca273c6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_ReadBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone
import Theorems.Thm_QEC_Coding_BDL26HistorySyndromeSensitivity_actualInputs_interval


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedHistoryQueryCone
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26PairedHistoryQueryCone
theorem _root_.solution (s t : TopInput S n) (a b : LevelIndex n)
    (ha : b.val ≤ a.val) (hs : actualInputs S n s a = actualInputs S n t a) :
    actualInputs S n s b = actualInputs S n t b := by
  rw [actualInputs_interval S n s a b ha,actualInputs_interval S n t a b ha,hs]
end QEC.Coding.BDL26PairedHistoryQueryCone
