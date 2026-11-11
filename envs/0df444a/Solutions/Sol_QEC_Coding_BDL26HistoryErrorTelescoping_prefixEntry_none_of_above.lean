-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.prefixEntry_none_of_above
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T10:31:51.355682+00:00
-- url     : https://prove2.me/submissions/05cb9e65-16ae-4cd0-95e7-a99693660bd7

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
    (b : LevelIndex depth) (e : CorrectionHistoryEntry D) (h : ¬ e.level ≤ b.val) :
    prefixEntry D b e = none := by
  cases e with
  | base B => exact False.elim (h (Nat.zero_le _))
  | step i O => exact dif_neg h
end QEC.Coding.BDL26HistoryErrorTelescoping
