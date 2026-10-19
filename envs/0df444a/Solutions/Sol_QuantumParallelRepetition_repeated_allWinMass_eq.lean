-- Prove2me | solution 1 for QuantumParallelRepetition.repeated_allWinMass_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/ebf101a0-178e-4c75-9170-4b90ada8eeec

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_strategyEventLaw_winEvent
import Theorems.Thm_QuantumParallelRepetition_repeated_allWinEvent_eq

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
noncomputable section
open scoped BigOperators
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) :
    (strategyEventLaw (G.repeat n) S).eventMass
      (FiniteEventLaw.winEvent (repeatedCoordinateWin G n)
        (Finset.univ : Finset (Fin n))) =
      S.winProbability := by
  rw [repeated_allWinEvent_eq]
  exact strategyEventLaw_winEvent (G.repeat n) S
end QuantumParallelRepetition
