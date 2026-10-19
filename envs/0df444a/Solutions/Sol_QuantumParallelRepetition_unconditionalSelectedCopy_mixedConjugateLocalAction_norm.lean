-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalSelectedCopy_mixedConjugateLocalAction_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.186359+00:00
-- url     : https://prove2.me/submissions/bf0f40b2-3b2c-4618-8947-3764c3c37575

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
    {d B m : ℕ}
    (U V : Matrix.unitaryGroup (Fin d) ℂ)
    (z : EuclideanSpace ℂ
      ((Σ _ : Fin B × Fin d, Fin m) ×
       (Σ _ : Fin B × Fin d, Fin m))) :
    ‖unconditionalMixedConjugateSigmaLocalAction B U V z‖ = ‖z‖ := by
  simpa [unconditionalMixedConjugateSigmaLocalAction] using
    dSVUniformDensityMixedProtocolLocalAction_norm
      (unconditionalMixedConjugateSigmaAtomLift (m := m) B U)
      (unconditionalMixedConjugateSigmaAtomLift (m := m) B V) z
end QuantumParallelRepetition
