-- Prove2me | solution 1 for QuantumParallelRepetition.pdfExistsRepeatedStrategyAboveExponential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/c9aca082-feaf-42ae-ae34-3bbe7e2e74ee

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_exists_repeatedStrategy_of_lt_entangledValue

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    (G : Game X Y A B) (n : ℕ) (d : ℝ)
    (failure : Real.exp (-d * (n : ℝ)) < repeatedEntangledValue G n) :
    ∃ S : Strategy (G.repeat n),
      Real.exp (-d * (n : ℝ)) < S.winProbability :=
  exists_repeatedStrategy_of_lt_entangledValue
    G (Real.exp_pos _) failure
end QuantumParallelRepetition
