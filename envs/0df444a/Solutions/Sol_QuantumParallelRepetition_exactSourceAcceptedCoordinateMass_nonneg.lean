-- Prove2me | solution 1 for QuantumParallelRepetition.exactSourceAcceptedCoordinateMass_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/2778d096-5c7d-4706-871d-8104d427310c

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
    0 ≤ exactSourceAcceptedCoordinateMass G n S D t := by
  unfold exactSourceAcceptedCoordinateMass
  apply Finset.sum_nonneg
  intro q _
  split
  · exact exactPostselectedJointLaw_nonneg
      G n S D positive q
  · exact le_rfl
end QuantumParallelRepetition
