-- Prove2me | solution 1 for QuantumParallelRepetition.exactSourceAcceptedCoordinateMass_le_law
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/b17347fe-8d9c-446c-bf13-18da30c0503f

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
    (D : Finset (Fin n))
    (positive : 0 < repeatedPostselectionMass G n S D)
    (t : ExactLocallySampleableTuple X Y A B D) :
    exactSourceAcceptedCoordinateMass G n S D t ≤
      exactLocallySampleableLaw G n S D t := by
  classical
  unfold exactSourceAcceptedCoordinateMass
    exactLocallySampleableLaw exactSourcePushforward
    groupedMass
  rw [Finset.sum_filter]
  apply Finset.sum_le_sum
  intro q _
  by_cases history : exactLocallySampleableCode D q = t
  · by_cases winning :
      repeatedCoordinateWin G n q.1.coordinate.val q.2 = true
    · simp [history, winning]
    · simp [history, winning,
        exactPostselectedJointLaw_nonneg
          G n S D positive q]
  · simp [history]
end QuantumParallelRepetition
