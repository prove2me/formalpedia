-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalMixedConjugateSelectedBranch_tensor_smul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/fe01e4d8-981d-4d8e-afee-a9fbb16188f4

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
namespace QuantumParallelRepetition
theorem _root_.solution
    {s τ : Type*} [Fintype s] [Fintype τ]
    (c : ℝ) (stage : EuclideanSpace ℂ s)
    (work : EuclideanSpace ℂ τ) :
    c • unconditionalMatchedVerifierTensor stage work =
      unconditionalMatchedVerifierTensor
        (c • stage) work := by
  ext ⟨a, b⟩
  change (c : ℂ) * (stage a * work b) =
    ((c : ℂ) * stage a) * work b
  ring
end QuantumParallelRepetition
