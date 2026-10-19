-- Prove2me | solution 1 for QuantumParallelRepetition.Strategy.winProbability_eq_winningEffect_born
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/d8925690-f936-4be3-a4ea-574d9f2f67ca

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_Strategy_winningEffect_born

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
    (S : Strategy G) :
    S.winProbability =
      ∑ x : X, ∑ y : Y,
        G.questionWeight x y *
          (Matrix.trace (S.state.matrix * S.winningEffect x y)).re := by
  simp_rw [S.winningEffect_born]
  rfl
end QuantumParallelRepetition.Strategy
