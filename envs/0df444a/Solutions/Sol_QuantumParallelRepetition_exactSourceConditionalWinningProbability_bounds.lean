-- Prove2me | solution 1 for QuantumParallelRepetition.exactSourceConditionalWinningProbability_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/226ffae9-d67a-4bb8-a6d6-20bcdb05d5e0

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
    0 ≤ exactSourceConditionalWinningProbability
      G n S D t ∧
    exactSourceConditionalWinningProbability
      G n S D t ≤ 1 := by
  have mass_nonnegative :=
    exactSourceAcceptedCoordinateMass_nonneg
      G n S D positive t
  have mass_le := exactSourceAcceptedCoordinateMass_le_law
    G n S D positive t
  have law_nonnegative := exactLocallySampleableLaw_nonneg
    G n S D positive t
  unfold exactSourceConditionalWinningProbability
  constructor
  · exact div_nonneg mass_nonnegative law_nonnegative
  · by_cases zero : exactLocallySampleableLaw G n S D t = 0
    · simp [zero]
    · exact (div_le_one
        (lt_of_le_of_ne law_nonnegative (Ne.symm zero))).mpr mass_le
end QuantumParallelRepetition
