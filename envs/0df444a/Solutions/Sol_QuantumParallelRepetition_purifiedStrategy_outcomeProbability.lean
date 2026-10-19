-- Prove2me | solution 1 for QuantumParallelRepetition.purifiedStrategy_outcomeProbability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/3fce9203-00d0-4a6f-90d2-444b96135b4f

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_pureVectorStrategy_outcomeProbability

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
namespace QuantumParallelRepetition
theorem _root_.solution
    {X Y A B : Type*}
    [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
    {G : Game X Y A B} (S : Strategy G)
    (x : X) (y : Y) (a : A) (b : B) :
    (purifiedStrategy S).outcomeProbability x y a b =
      S.outcomeProbability x y a b := by
  unfold purifiedStrategy
  rw [pureVectorStrategy_outcomeProbability]
  exact strategyPurificationVector_quadratic S
    ((S.aliceMeasurement x).effect a)
    ((S.bobMeasurement y).effect b)
end QuantumParallelRepetition
