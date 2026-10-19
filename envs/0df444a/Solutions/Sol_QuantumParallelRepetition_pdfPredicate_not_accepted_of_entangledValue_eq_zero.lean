-- Prove2me | solution 1 for QuantumParallelRepetition.pdfPredicate_not_accepted_of_entangledValue_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/763ba7ce-0bfa-4bea-9204-e170c7d209f2

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_winProbabilities_bddAbove
import Theorems.Thm_QuantumParallelRepetition_pdfQuestionWeight_le_constantStrategy

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    (G : Game X Y A B)
    (zero : entangledValue G = 0)
    (x : X) (y : Y) (a : A) (b : B)
    (supported : 0 < G.questionWeight x y) :
    G.predicate x y a b ≠ true := by
  intro accepted
  have lower := pdfQuestionWeight_le_constantStrategy
    G x y a b accepted
  have upper :
      (pdfConstantStrategy G a b).winProbability ≤
        entangledValue G := by
    unfold entangledValue
    exact le_csSup (winProbabilities_bddAbove G)
      ⟨pdfConstantStrategy G a b, rfl⟩
  linarith
end QuantumParallelRepetition
