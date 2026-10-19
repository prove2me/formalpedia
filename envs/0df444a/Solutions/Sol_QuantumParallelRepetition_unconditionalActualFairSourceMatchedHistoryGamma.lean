-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFairSourceMatchedHistoryGamma
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/2ce7d843-dbf9-4564-a96d-2f667e3d294e

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalExactFairGammaUnit_eq_global
import Theorems.Thm_QuantumParallelRepetition_unconditionalFairMatchedFlag_aliceTarget_eq_aliceSample

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
open QuantumParallelRepetition.ClassicalSampling
namespace QuantumParallelRepetition
theorem _root_.solution
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    (G : Game X Y A B) (n : ℕ) (S : Strategy (G.repeat n))
    (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (flag : ExactSourceSharedFlag X Y A B D denominator)
    (x : X) (y : Y) :
    unconditionalExactFairGammaUnit G n S D
        (exactSourceAliceSampleTuple
          D denominator numerator nonempty (flag, (x, y))) =
      unconditionalActualFairSourceAliceTarget
        G n S D denominator numerator nonempty flag x := by
  rw [unconditionalExactFairGammaUnit_eq_global]
  exact
    (unconditionalFairMatchedFlag_aliceTarget_eq_aliceSample
      G n S D denominator numerator nonempty flag x y).symm
end QuantumParallelRepetition
