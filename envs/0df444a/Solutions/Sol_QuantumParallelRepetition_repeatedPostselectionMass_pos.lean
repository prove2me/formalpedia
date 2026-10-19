-- Prove2me | solution 1 for QuantumParallelRepetition.repeatedPostselectionMass_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/2415d28e-4041-4e29-8411-27b9ae010cad

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_repeated_winProbability_le_postselectionMass

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
    (S : Strategy (G.repeat n)) (C : Finset (Fin n))
    (hwin : 0 < S.winProbability) :
    0 < repeatedPostselectionMass G n S C :=
  lt_of_lt_of_le hwin
    (repeated_winProbability_le_postselectionMass G n S C)
end QuantumParallelRepetition
