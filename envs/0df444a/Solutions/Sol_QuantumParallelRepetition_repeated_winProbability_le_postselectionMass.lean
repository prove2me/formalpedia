-- Prove2me | solution 1 for QuantumParallelRepetition.repeated_winProbability_le_postselectionMass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/aa03315d-49d2-49e6-860b-2decd0c85f2c

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_repeated_allWinMass_eq
import Theorems.Thm_QuantumParallelRepetition_allWinMass_le_postselectionMass

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    (G : Game X Y A B) (n : ℕ)
    (S : Strategy (G.repeat n)) (C : Finset (Fin n)) :
    S.winProbability ≤ repeatedPostselectionMass G n S C := by
  rw [← repeated_allWinMass_eq G n S]
  exact allWinMass_le_postselectionMass
    (strategyEventLaw (G.repeat n) S) (repeatedCoordinateWin G n) C
end QuantumParallelRepetition
