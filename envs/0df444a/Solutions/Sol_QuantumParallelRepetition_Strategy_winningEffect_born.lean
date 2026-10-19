-- Prove2me | solution 1 for QuantumParallelRepetition.Strategy.winningEffect_born
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/b9911ec6-0738-4746-b441-b90051fc369e

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open QuantumParallelRepetition.Strategy
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {G : Game X Y A B}
namespace QuantumParallelRepetition.Strategy
theorem _root_.solution
    (S : Strategy G) (x : X) (y : Y) :
    (Matrix.trace (S.state.matrix * S.winningEffect x y)).re =
      ∑ a : A, ∑ b : B,
        if G.predicate x y a b = true then
          S.outcomeProbability x y a b else 0 := by
  classical
  simp [winningEffect, outcomeProbability, Matrix.mul_sum,
    Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  split <;> simp
end QuantumParallelRepetition.Strategy
