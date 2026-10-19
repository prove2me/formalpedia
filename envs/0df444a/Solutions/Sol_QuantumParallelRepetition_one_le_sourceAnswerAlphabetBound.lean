-- Prove2me | solution 1 for QuantumParallelRepetition.one_le_sourceAnswerAlphabetBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.858309+00:00
-- url     : https://prove2.me/submissions/371d01fb-e831-4063-bd26-bf8db0e38d4e

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators InnerProductSpace
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    (A B : Type*) [Fintype A] [Fintype B] :
    1 ≤ sourceAnswerAlphabetBound A B := by
  exact le_max_left _ _
end QuantumParallelRepetition
