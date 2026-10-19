-- Prove2me | solution 1 for QuantumParallelRepetition.pureVectorStrategy_outcomeProbability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/7b7bfbcb-8f78-4d4e-8915-b3edabe60c99

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
namespace QuantumParallelRepetition
theorem _root_.solution
    {X Y A B : Type*} {dA dB : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    [Fintype dA] [Fintype dB] [DecidableEq dA] [DecidableEq dB]
    (G : Game X Y A B)
    (z : EuclideanSpace ℂ (dA × dB)) (hz : ‖z‖ = 1)
    (PA : X → POVM A dA) (PB : Y → POVM B dB)
    (x : X) (y : Y) (a : A) (b : B) :
    (pureVectorStrategy G z hz PA PB).outcomeProbability x y a b =
      quadraticExpectation
        (Matrix.toEuclideanCLM (n := dA × dB) (𝕜 := ℂ)
          ((PA x).effect a ⊗ₖ (PB y).effect b)) z := by
  change
    (Matrix.trace
      ((pureDensityMatrix z hz).matrix *
        ((PA x).effect a ⊗ₖ (PB y).effect b))).re = _
  exact pureDensityMatrix_trace_mul z hz
    ((PA x).effect a ⊗ₖ (PB y).effect b)
end QuantumParallelRepetition
