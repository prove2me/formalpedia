-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.balance_full_word
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:44:13.24443+00:00
-- url     : https://prove2.me/submissions/f2d0cf61-0218-4d21-9a4e-fd9620027a1b

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping
import Theorems.Thm_QEC_Coding_BDL26HistoryErrorTelescoping_word_add_self
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open scoped Classical
universe u v w
namespace QEC.Coding.BDL26HistoryErrorTelescoping
theorem _root_.solution {I : Type u} (x y c k p : Word BDL26Field I)
    (h : x=y+c+p) : y+(c+k)=x+k+p := by
  rw [h]
  symm
  calc
    (y+c+p)+k+p = (y+(c+k))+(p+p) := by ac_rfl
    _ = y+(c+k) := by rw [word_add_self,add_zero]
end QEC.Coding.BDL26HistoryErrorTelescoping
