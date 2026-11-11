-- Prove2me | solution 1 for QEC.Coding.BDL26HistorySyndromeSensitivity.propagate_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T06:43:23.275196+00:00
-- url     : https://prove2.me/submissions/c1f6353f-9c86-42bf-8e40-e4282e114004

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Snapshots
import Mathlib.Order.Interval.Finset.Nat
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity_Intervals

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open MultiscaleDecoder
open scoped Classical
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistorySyndromeSensitivity
theorem _root_.solution (b : Nat) (hb : b+1 ≤ n) (a : LevelIndex n)
    (ha : a.val ≤ b) (A : Finset (Coordinates S n ⟨b+1,Nat.lt_succ_of_le hb⟩)) :
    propagate S n (b+1) hb a (by omega) A =
      propagate S n b (by omega) a ha
        (stepPropagation S (n+2) (LevelTwoHistory.physicalStep ⟨b,by omega⟩) A) := by
  have hne : ¬ a.val = b+1 := by omega
  rw [propagate]
  exact dif_neg hne
end QEC.Coding.BDL26HistorySyndromeSensitivity
