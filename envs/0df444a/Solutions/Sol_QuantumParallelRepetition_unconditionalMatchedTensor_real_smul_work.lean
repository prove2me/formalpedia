-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalMatchedTensor_real_smul_work
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/28f42142-27fb-4817-a5f7-ab299eee6f97

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators Kronecker ComplexOrder MatrixOrder
  Matrix.Norms.L2Operator InnerProductSpace
namespace QuantumParallelRepetition
theorem _root_.solution
    {s t : Type*} [Fintype s] [Fintype t]
    (c : ℝ)
    (stage : EuclideanSpace ℂ s)
    (work : EuclideanSpace ℂ t) :
    c • unconditionalMatchedVerifierTensor stage work =
      unconditionalMatchedVerifierTensor stage (c • work) := by
  ext q
  change (c : ℂ) * (stage q.1 * work q.2) =
    stage q.1 * ((c : ℂ) * work q.2)
  ring
end QuantumParallelRepetition
