-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.snapshotWords_zero_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T08:12:48.675207+00:00
-- url     : https://prove2.me/submissions/3d904893-e16e-4b43-9603-1c1070744a9a

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
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryErrorTelescoping
theorem _root_.solution (sigma : TopInput S n) (a : LevelIndex n)
    (ha : a.val ≤ 0) : snapshotWords S n sigma a 0 (Nat.zero_le _) ha = [] := by
  rw [snapshotWords] <;> rfl
end QEC.Coding.BDL26HistoryErrorTelescoping
