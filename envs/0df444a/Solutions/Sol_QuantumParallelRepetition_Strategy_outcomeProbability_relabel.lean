-- Prove2me | solution 1 for QuantumParallelRepetition.Strategy.outcomeProbability_relabel
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-12T02:06:43.547898+00:00
-- url     : https://prove2.me/submissions/bf3ea93b-b0e4-4dc4-833c-b1c0b04a7545

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_alphabet_relabelling
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic

open scoped BigOperators
open QuantumParallelRepetition

variable {X Y A B X' Y' A' B' : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']

theorem solution
    {G : Game X Y A B} {H : Game X' Y' A' B'}
    (S : Strategy G) (eX : X ≃ X') (eY : Y ≃ Y') (eA : A ≃ A') (eB : B ≃ B')
    (x' : X') (y' : Y') (a' : A') (b' : B') :
    (S.relabel (H := H) eX eY eA eB).outcomeProbability x' y' a' b' =
      S.outcomeProbability (eX.symm x') (eY.symm y') (eA.symm a') (eB.symm b') := by
  rfl
