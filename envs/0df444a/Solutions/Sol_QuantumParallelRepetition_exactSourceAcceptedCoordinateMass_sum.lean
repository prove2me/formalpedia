-- Prove2me | solution 1 for QuantumParallelRepetition.exactSourceAcceptedCoordinateMass_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/aaf8ee3c-d71d-482c-b28c-91c0358af254

import Mathlib
import Definitions.Def_QuantumParallelRepetition

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
    (D : Finset (Fin n)) :
    (∑ t : ExactLocallySampleableTuple X Y A B D,
      exactSourceAcceptedCoordinateMass G n S D t) =
      ∑ q : ExactJointOutcome X Y A B D,
        if repeatedCoordinateWin G n q.1.coordinate.val q.2 = true
        then exactPostselectedJointLaw G n S D q
        else 0 := by
  classical
  unfold exactSourceAcceptedCoordinateMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  by_cases winning :
      repeatedCoordinateWin G n q.1.coordinate.val q.2 = true
  · simp [winning]
  · simp [winning]
end QuantumParallelRepetition
