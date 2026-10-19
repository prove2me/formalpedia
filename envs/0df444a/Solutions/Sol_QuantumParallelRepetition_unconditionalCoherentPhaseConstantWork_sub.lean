-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalCoherentPhaseConstantWork_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/6d411860-1ebb-4f60-b8c4-0a8364441288

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
    {H : Type*} [Fintype H] {B m : ℕ}
    (x y : EuclideanSpace ℂ (H × H))
    (work : EuclideanSpace ℂ (Fin m × Fin m)) :
    dSVDensityRationalPublicBucketCoherentPhaseSigmaState
        B x (fun _ _ _ => work) -
      dSVDensityRationalPublicBucketCoherentPhaseSigmaState
        B y (fun _ _ _ => work) =
      dSVDensityRationalPublicBucketCoherentPhaseSigmaState
        B (x - y) (fun _ _ _ => work) := by
  ext ⟨⟨⟨φ, i⟩, a⟩, ⟨⟨ψ, j⟩, b⟩⟩
  change
    (ePRState B (φ, ψ) * x (i, j)) * work (a, b) -
      (ePRState B (φ, ψ) * y (i, j)) * work (a, b) =
      (ePRState B (φ, ψ) *
        (x (i, j) - y (i, j))) * work (a, b)
  ring
end QuantumParallelRepetition
