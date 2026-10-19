-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFairSourceMatchedHistoryPhi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:19.890976+00:00
-- url     : https://prove2.me/submissions/cf13d496-8b3a-4da4-8018-c3aa7465c555

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalFairMatchedFlag_bobTarget_eq_aliceSample

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
    (x : X) (y : Y)
    (matching :
      exactSourcePermutationMatched
        D denominator numerator nonempty (flag, (x, y)) = true) :
    exactGlobalHistoryFinPhi G n S D
        (exactSourceAliceSampleTuple
          D denominator numerator nonempty (flag, (x, y))).2.2.2 y =
      unconditionalActualFairSourceBobTarget
        G n S D denominator numerator nonempty flag y := by
  exact
    (unconditionalFairMatchedFlag_bobTarget_eq_aliceSample
      G n S D denominator numerator nonempty flag x y matching).symm
end QuantumParallelRepetition
