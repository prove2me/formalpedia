-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalSourcePhysicalStoppingBranch_sigmaContinuation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/7430385b-d226-46a7-8a6f-2549c6f15d14

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
    {R κ : Type} [Fintype R] [DecidableEq R]
    [Fintype κ] [DecidableEq κ]
    (U V : R → Matrix.unitaryGroup κ ℂ)
    (z : EuclideanSpace ℂ ((Σ _ : R, κ) × (Σ _ : R, κ)))
    (r s : R) :
    actualStoppingBranchVector
      (dSVUniformDensityPhysicalAsyncSigmaContinuation U V z)
      r s =
      toLp 2
        ((((U r : Matrix κ κ ℂ) ⊗ₖ (V s : Matrix κ κ ℂ)).mulVec
          (ofLp (actualStoppingBranchVector z r s)))) := by
  classical
  ext ⟨i, j⟩
  simp [actualStoppingBranchVector,
    dSVUniformDensityPhysicalAsyncSigmaContinuation,
    coherentSharedRandomControlledUnitary,
    Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
    Matrix.blockDiagonal'_apply,
    Fintype.sum_prod_type, Fintype.sum_sigma]
end QuantumParallelRepetition
