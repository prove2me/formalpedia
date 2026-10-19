-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalFairMatchedFlag_history_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/513c6705-c636-4c52-8a33-7742d60ff4e0

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open scoped BigOperators
open QuantumParallelRepetition.ClassicalSampling
namespace QuantumParallelRepetition
theorem _root_.solution
    {X Y A B : Type}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {n : ℕ} (D : Finset (Fin n)) (denominator : ℕ)
    (numerator : ExactLocalSamplerIndex X Y D →
      ExactHistoryFlag X Y A B D → ℕ)
    (nonempty : ∀ index,
      (rationalMarked denominator (numerator index)).Nonempty)
    (flag : ExactSourceSharedFlag X Y A B D denominator)
    (x : X) (y : Y)
    (matched :
      exactSourcePermutationMatched
        D denominator numerator nonempty (flag, (x, y)) = true) :
    exactSourceAlicePermutationHistory
        D denominator numerator nonempty flag x =
      exactSourceBobPermutationHistory
        D denominator numerator nonempty flag y := by
  classical
  change
    decide
      (exactSourceAlicePermutationHistory
          D denominator numerator nonempty flag x =
        exactSourceBobPermutationHistory
          D denominator numerator nonempty flag y) = true at matched
  exact of_decide_eq_true matched
end QuantumParallelRepetition
