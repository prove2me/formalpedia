-- Prove2me | solution 1 for QEC.Coding.BDL26HistoryErrorTelescoping.accumulatedPotential_succ_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T11:20:25.176436+00:00
-- url     : https://prove2.me/submissions/9e05a0ba-2dde-47b8-a0d4-62247e7d19d2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping_HistorySums
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistorySyndromeSensitivity
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_HistoryErrorTelescoping

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26HistoryErrorTelescoping
open MultiscaleDecoder BDL26HistorySyndromeSensitivity
open BDL26FiniteTannerSquare BDL26IndexedDecoder BDL26OwnerIncidenceMasks
open scoped Classical
universe u v w
variable (S : OddScale) (n : Nat)
namespace QEC.Coding.BDL26HistoryErrorTelescoping
theorem _root_.solution (b : LevelIndex n)
    (u : (SuffixData S n).family.Cochain1 b) (a : LevelIndex n)
    (c : Nat) (hc : c+1 ≤ b.val) (ha : a.val ≤ c+1) :
    accumulatedPotential S n b u a (c+1) hc ha =
      if h : a.val = c+1 then 0 else
        let i : StepIndex n := ⟨c,Nat.lt_of_lt_of_le
          (Nat.lt_of_lt_of_le (Nat.lt_succ_self c) hc) (Nat.le_of_lt_succ b.isLt)⟩
        ((SuffixData S n).selectedMap i).map0
          (accumulatedPotential S n b u a c (by omega) (by omega)) +
            descentPotential S n b u i (by change c < b.val; omega) := by
  rw [accumulatedPotential] <;> rfl
end QEC.Coding.BDL26HistoryErrorTelescoping
