-- Prove2me | solution 1 for QuantumParallelRepetition.repeated_allWinEvent_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/ec357931-0522-4859-917b-2bef1a8c9773

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
noncomputable section
open scoped BigOperators
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    (G : Game X Y A B) (n : ℕ) :
    FiniteEventLaw.winEvent (repeatedCoordinateWin G n)
      (Finset.univ : Finset (Fin n)) =
      strategyWinEvent (G.repeat n) := by
  classical
  ext ω
  simp [FiniteEventLaw.winEvent, strategyWinEvent,
    repeatedCoordinateWin, Game.repeat_predicate_eq_true]
end QuantumParallelRepetition
