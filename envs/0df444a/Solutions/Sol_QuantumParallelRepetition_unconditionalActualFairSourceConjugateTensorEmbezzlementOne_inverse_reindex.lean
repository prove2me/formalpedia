-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualFairSourceConjugateTensorEmbezzlementOne_inverse_reindex
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/384b584f-fa45-46cb-89bc-1a30149e9359

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalActualFairSourceTensorEmbezzlementOne_reindex

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
    {d : ℕ} (ξ : BipartiteUnitVector d) :
    LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (Equiv.prodCongr
          (finCongr (Nat.mul_one d)).symm
          (finCongr (Nat.mul_one d)).symm)
        (unconditionalConjugatePureVector ξ.val) =
      unconditionalConjugatePureVector
        (tensorEmbezzlementTarget (n := 1) ξ) := by
  classical
  ext ⟨i, j⟩
  change
    star (ξ.val
      ((finCongr (Nat.mul_one d)) i,
       (finCongr (Nat.mul_one d)) j)) =
      star (tensorEmbezzlementTarget (n := 1) ξ (i, j))
  congr 1
  have recovered := congrArg
    (fun z : EuclideanSpace ℂ (Fin d × Fin d) =>
      z ((finCongr (Nat.mul_one d)) i,
         (finCongr (Nat.mul_one d)) j))
    (unconditionalActualFairSourceTensorEmbezzlementOne_reindex ξ)
  simpa [LinearIsometryEquiv.piLpCongrLeft_apply] using recovered.symm
end QuantumParallelRepetition
