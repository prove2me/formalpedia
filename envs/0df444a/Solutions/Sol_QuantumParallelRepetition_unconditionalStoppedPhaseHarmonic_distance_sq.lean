-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalStoppedPhaseHarmonic_distance_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/09149827-f130-4aec-8dd0-09e17b2a4e70

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_unconditionalSelectedCopy_coherentPhaseConstantWork_norm_sq
import Theorems.Thm_QuantumParallelRepetition_unconditionalCoherentPhaseConstantWork_sub

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
    (phases : 0 < B) (harmonic : 0 < m)
    (x y : EuclideanSpace ℂ (H × H)) :
    ‖dSVDensityRationalPublicBucketCoherentPhaseSigmaState
        B x (fun _ _ _ => embezzlementState m) -
      dSVDensityRationalPublicBucketCoherentPhaseSigmaState
        B y (fun _ _ _ => embezzlementState m)‖ ^ 2 =
      ‖x - y‖ ^ 2 := by
  rw [unconditionalCoherentPhaseConstantWork_sub,
    unconditionalSelectedCopy_coherentPhaseConstantWork_norm_sq
      phases,
    embezzlementState_norm m harmonic]
  ring
end QuantumParallelRepetition
