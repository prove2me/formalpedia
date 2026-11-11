-- Prove2me | solution 1 for QEC.Coding.BDL26HistorySyndromeSensitivity.physical_stepFactor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T09:54:09.565198+00:00
-- url     : https://prove2.me/submissions/38d9bca7-e481-4d53-9eea-b66e1c4d618c

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
theorem _root_.solution (b : Nat) (hb : b < n) :
    stepFactor (n+2) (LevelTwoHistory.physicalStep (⟨b,hb⟩ : StepIndex n)) =
      if b % 2 = 0 then 57 else 1 := by
  change (if (b+2) % 2 = 0 then 57 else 1) = if b % 2 = 0 then 57 else 1
  have hp : (b+2) % 2 = b % 2 := by omega
  exact congrArg (fun r : Nat => if r = 0 then 57 else 1) hp
end QEC.Coding.BDL26HistorySyndromeSensitivity
