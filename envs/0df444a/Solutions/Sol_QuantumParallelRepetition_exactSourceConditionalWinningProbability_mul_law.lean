-- Prove2me | solution 1 for QuantumParallelRepetition.exactSourceConditionalWinningProbability_mul_law
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/8f8074d7-cf89-48f8-b8bd-bea15232436b

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_exactSourceAcceptedCoordinateMass_nonneg
import Theorems.Thm_QuantumParallelRepetition_exactSourceAcceptedCoordinateMass_le_law

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
    exactLocallySampleableLaw G n S D t *
        exactSourceConditionalWinningProbability G n S D t =
      exactSourceAcceptedCoordinateMass G n S D t := by
  by_cases zero : exactLocallySampleableLaw G n S D t = 0
  · have nonnegative := exactSourceAcceptedCoordinateMass_nonneg
      G n S D positive t
    have bounded := exactSourceAcceptedCoordinateMass_le_law
      G n S D positive t
    rw [zero] at bounded
    have accepted_zero :
        exactSourceAcceptedCoordinateMass G n S D t = 0 := by
      linarith
    simp [zero, accepted_zero]
  · unfold exactSourceConditionalWinningProbability
    field_simp [zero]
end QuantumParallelRepetition
