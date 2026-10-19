-- Prove2me | solution 1 for QuantumParallelRepetition.exactSourceConditionalWinningProbability_expectation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/32f52447-b65f-43b6-a524-e256c39704d6

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_exactSourceConditionalWinningProbability_mul_law
import Theorems.Thm_QuantumParallelRepetition_exactSourceAcceptedCoordinateMass_sum

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048
open QuantumParallelRepetition.ClassicalInformation
attribute [local instance] Classical.propDecidable
variable {X Y A B : Type*}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
namespace QuantumParallelRepetition
theorem _root_.solution
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D) :
    (∑ t : ExactLocallySampleableTuple X Y A B D,
      exactLocallySampleableLaw G n S D t *
        exactSourceConditionalWinningProbability G n S D t) =
      ∑ q : ExactJointOutcome X Y A B D,
        if repeatedCoordinateWin G n q.1.coordinate.val q.2 = true
        then exactPostselectedJointLaw G n S D q
        else 0 := by
  simp_rw [exactSourceConditionalWinningProbability_mul_law
    G n S D positive]
  exact exactSourceAcceptedCoordinateMass_sum G n S D
end QuantumParallelRepetition
