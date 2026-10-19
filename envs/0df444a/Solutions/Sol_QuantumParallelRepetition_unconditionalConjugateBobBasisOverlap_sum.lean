-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalConjugateBobBasisOverlap_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/78e0dd3a-9ef8-4850-ae5c-f7cec911956b

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalConjugateBobBasisOverlapCancellation

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
    {d : ℕ} (U V : Matrix.unitaryGroup (Fin d) ℂ)
    (i b : Fin d) :
    (∑ j : Fin d,
      unitaryBasisOverlap U V i j *
        star ((V : Matrix (Fin d) (Fin d) ℂ) b j)) =
      star ((U : Matrix (Fin d) (Fin d) ℂ) b i) := by
  have identity := congrArg
    (fun M : Matrix (Fin d) (Fin d) ℂ => M i b)
    (unconditionalConjugateBobBasisOverlapCancellation U V)
  simpa [Matrix.mul_apply, Matrix.transpose_apply,
    conjugateUnitary_apply] using identity
end QuantumParallelRepetition
