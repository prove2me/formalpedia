-- Prove2me | solution 1 for QEC.Coding.BDL26PairedHistoryQueryCone.queries_self
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:01:48.70488+00:00
-- url     : https://prove2.me/submissions/7d681583-08da-4aef-9855-079b5e8a1b4a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone_ReadBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_PairedHistoryQueryCone

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26PairedHistoryQueryCone
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26IndexedDecoder
open BDL26OwnerIncidenceMasks BDL26HistorySyndromeSensitivity
open BDL26HistoryErrorTelescoping MultiscaleDecoder
open scoped Classical BigOperators
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26PairedHistoryQueryCone
theorem _root_.solution (e : TopWord S n) (a : LevelIndex n) :
    queries S n e a a = querySeed S n e a := by
  rcases a with ⟨a,ha⟩
  cases a with
  | zero => rw [queries,queryPrefix]; exact dif_pos rfl
  | succ a => rw [queries,queryPrefix]; exact dif_pos rfl
end QEC.Coding.BDL26PairedHistoryQueryCone
