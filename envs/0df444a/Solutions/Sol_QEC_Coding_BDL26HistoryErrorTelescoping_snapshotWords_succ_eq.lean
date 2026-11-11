-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.snapshotWords_succ_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T08:12:51.506636+00:00
-- url     : https://prove2.me/submissions/e65886c3-e0c6-413a-812b-285826711935

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
    (b : Nat) (hb : b+1 ≤ n) (ha : a.val ≤ b+1) :
    snapshotWords S n sigma a (b+1) hb ha =
      if h : a.val = b+1 then [] else
        let i : StepIndex n := ⟨b,Nat.lt_of_lt_of_le (Nat.lt_succ_self b) hb⟩
        (actualOutput S n sigma i).correction ::
          (snapshotWords S n sigma a b (by omega) (by omega)).map
            ((SuffixData S n).selectedMap i).map1 := by
  rw [snapshotWords] <;> rfl
end QEC.Coding.BDL26HistoryErrorTelescoping
