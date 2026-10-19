-- Prove2me | solution 1 for QuantumParallelRepetition.pureVectorWinningProbability_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/1c4780b0-f8c0-47e1-ac4a-cc0fa073ff86

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_Strategy_winProbability_eq_winningEffect_born

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
variable {X Y A B dA dB J : Type}
variable [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]
variable [Fintype J] [DecidableEq J]
namespace QuantumParallelRepetition
theorem _root_.solution
    (G : Game X Y A B)
    (z : EuclideanSpace ℂ (dA × dB)) (hz : ‖z‖ = 1)
    (PA : X → POVM A dA) (PB : Y → POVM B dB) :
    (pureVectorStrategy G z hz PA PB).winProbability =
      ∑ x : X, ∑ y : Y, G.questionWeight x y *
        quadraticExpectation
          (Matrix.toEuclideanCLM (n := dA × dB) (𝕜 := ℂ)
            (pureVerifierEffect G z hz PA PB x y)) z := by
  classical
  rw [(pureVectorStrategy G z hz PA PB).winProbability_eq_winningEffect_born]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  exact pureDensityMatrix_trace_mul z hz
    (pureVerifierEffect G z hz PA PB x y)
end QuantumParallelRepetition
