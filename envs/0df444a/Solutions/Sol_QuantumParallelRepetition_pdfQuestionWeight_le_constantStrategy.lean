-- Prove2me | solution 1 for QuantumParallelRepetition.pdfQuestionWeight_le_constantStrategy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/d50f6c7b-597d-483d-8d8c-d5da411a50a5

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_pdfConstantStrategy_winProbability

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
    (x : X) (y : Y) (a : A) (b : B)
    (accepted : G.predicate x y a b = true) :
    G.questionWeight x y ≤
      (pdfConstantStrategy G a b).winProbability := by
  classical
  rw [pdfConstantStrategy_winProbability]
  calc
    G.questionWeight x y =
        if G.predicate x y a b = true then G.questionWeight x y else 0 := by
          simp [accepted]
    _ ≤ ∑ y' : Y,
        if G.predicate x y' a b = true then G.questionWeight x y' else 0 := by
          exact Finset.single_le_sum
            (f := fun y' : Y =>
              if G.predicate x y' a b = true then G.questionWeight x y' else 0)
            (fun y' _ => by split_ifs <;> simp [G.weight_nonneg])
            (Finset.mem_univ y)
    _ ≤ ∑ x' : X, ∑ y' : Y,
        if G.predicate x' y' a b = true then G.questionWeight x' y' else 0 := by
          exact Finset.single_le_sum
            (f := fun x' : X => ∑ y' : Y,
              if G.predicate x' y' a b = true then G.questionWeight x' y' else 0)
            (fun x' _ => Finset.sum_nonneg
              (fun y' _ => by split_ifs <;> simp [G.weight_nonneg]))
            (Finset.mem_univ x)
end QuantumParallelRepetition
