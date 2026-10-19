-- Prove2me | solution 1 for QuantumParallelRepetition.exactSource_failure_sum_lt_of_uniform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:16.465991+00:00
-- url     : https://prove2.me/submissions/3d0a870f-bbce-46a7-9c4b-0736f2b52907

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
    (remaining : 0 < (Finset.univ \ D).card)
    (positive : 0 < repeatedPostselectionMass G n S D)
    {δ : ℝ}
    (failure : uniformRemainingFailure
      (strategyEventLaw (G.repeat n) S)
      (repeatedCoordinateWin G n) D < δ) :
    (∑ i ∈ Finset.univ \ D,
      FiniteEventLaw.failureMass
        (strategyEventLaw (G.repeat n) S)
        (repeatedCoordinateWin G n) D i) <
      ((Finset.univ \ D).card : ℝ) *
        (δ * repeatedPostselectionMass G n S D) := by
  have cardinality : 0 < ((Finset.univ \ D).card : ℝ) := by
    exact_mod_cast remaining
  unfold uniformRemainingFailure conditionalCoordinateFailure at failure
  change
    (∑ i ∈ Finset.univ \ D,
      FiniteEventLaw.failureMass
        (strategyEventLaw (G.repeat n) S)
        (repeatedCoordinateWin G n) D i /
        repeatedPostselectionMass G n S D) /
      ((Finset.univ \ D).card : ℝ) < δ at failure
  rw [← Finset.sum_div] at failure
  have first := (div_lt_iff₀ cardinality).mp failure
  have second := (div_lt_iff₀ positive).mp first
  nlinarith
end QuantumParallelRepetition
