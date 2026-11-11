-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.word_toggle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:05:16.693325+00:00
-- url     : https://prove2.me/submissions/51b4e2ef-bc1c-46af-a8d2-21c0adc572d5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_word_add_self

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open scoped Classical
universe u v w
namespace QEC.Coding.BDL26HistoryErrorTelescoping
theorem _root_.solution {I : Type u} (x y p : Word BDL26Field I) (h : x=y+p) : y=x+p := by
  rw [h]
  calc
    y = y+(p+p) := by rw [word_add_self,add_zero]
    _ = y+p+p := by ac_rfl
end QEC.Coding.BDL26HistoryErrorTelescoping
