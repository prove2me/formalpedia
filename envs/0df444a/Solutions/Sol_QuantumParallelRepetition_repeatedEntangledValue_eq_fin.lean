-- Prove2me | solution 1 for QuantumParallelRepetition.repeatedEntangledValue_eq_fin
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-12T02:13:51.130339+00:00
-- url     : https://prove2.me/submissions/905b82a6-82e9-4176-b41b-c833e04fc3dc

import Definitions.Def_quantum_parallel_repetition_game
import Definitions.Def_qpr_alphabet_relabelling
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic
import Theorems.Thm_QuantumParallelRepetition_repeatedEntangledValue_relabel

open scoped BigOperators
open QuantumParallelRepetition

variable {X Y A B X' Y' A' B' : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype X'] [Fintype Y'] [Fintype A'] [Fintype B']

theorem solution
    (G : Game X Y A B) (n : ℕ) :
    repeatedEntangledValue G n
      = repeatedEntangledValue (G.relabel (Fintype.equivFin X) (Fintype.equivFin Y)
          (Fintype.equivFin A) (Fintype.equivFin B)) n := by
  exact (repeatedEntangledValue_relabel (Fintype.equivFin X) (Fintype.equivFin Y)
    (Fintype.equivFin A) (Fintype.equivFin B)
    (fun _ _ => by simp) (fun _ _ _ _ => by simp) n).symm
