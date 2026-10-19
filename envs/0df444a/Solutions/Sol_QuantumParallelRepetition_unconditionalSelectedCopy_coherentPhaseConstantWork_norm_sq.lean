-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalSelectedCopy_coherentPhaseConstantWork_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/e8048246-a5f2-469b-b3d2-8a58d66a8cd5

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalMixedCanonicalPrefixPhysicalSigmaWeighted_norm_sq
import Theorems.Thm_QuantumParallelRepetition_unconditionalSelectedCopy_coherentPhaseSigma_norm_sq

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
    {H : Type*} [Fintype H] {B m : ℕ}
    (phases : 0 < B)
    (history : EuclideanSpace ℂ (H × H))
    (work : EuclideanSpace ℂ (Fin m × Fin m)) :
    ‖dSVDensityRationalPublicBucketCoherentPhaseSigmaState
        B history (fun _ _ _ => work)‖ ^ 2 =
      ‖history‖ ^ 2 * ‖work‖ ^ 2 := by
  rw [unconditionalSelectedCopy_coherentPhaseSigma_norm_sq
    phases history (fun _ _ => work),
    dSVDensityRationalMixedCanonicalPrefixPhysicalSigmaWeighted_norm_sq]
  calc
    (∑ i : H, ∑ j : H, ‖history (i, j)‖ ^ 2 * ‖work‖ ^ 2) =
        (∑ i : H, ∑ j : H, ‖history (i, j)‖ ^ 2) * ‖work‖ ^ 2 := by
          simp_rw [Finset.sum_mul]
    _ = _ := by
      congr 1
      rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
end QuantumParallelRepetition
