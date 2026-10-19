-- Prove2me | solution 1 for QuantumParallelRepetition.pdfConstantStrategy_winProbability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.17122+00:00
-- url     : https://prove2.me/submissions/8eda17c2-1946-4603-b8ea-7c88b5f3d80a

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_pdfConstantStrategy_outcomeProbability

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
    (G : Game X Y A B) (a : A) (b : B) :
    (pdfConstantStrategy G a b).winProbability =
      ∑ x : X, ∑ y : Y,
        if G.predicate x y a b = true then G.questionWeight x y else 0 := by
  classical
  have accepted_outcome (x : X) (y : Y) (a' : A) (b' : B) :
      (if G.predicate x y a' b' = true then
        (if a' = a ∧ b' = b then (1 : ℝ) else 0)
      else 0) =
        if a' = a then
          if b' = b then
            if G.predicate x y a b = true then 1 else 0
          else 0
        else 0 := by
    by_cases alice : a' = a <;> by_cases bob : b' = b <;>
      simp_all
  unfold Strategy.winProbability
  simp_rw [pdfConstantStrategy_outcomeProbability]
  simp_rw [accepted_outcome]
  simp [mul_ite]
end QuantumParallelRepetition
