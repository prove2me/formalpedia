-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalPublicLogPhasePureSource_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/1ba5e717-81cc-455c-913e-468bc50455e3

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
    (B N d L : ℕ)
    (φ ψ : Fin B)
    (a b : DSVUniformDensityThresholdWholeHistoryLocalIndex
      N d L) :
    dSVDensityRationalPublicLogPhasePureSource
        B N d L ((φ, a), (ψ, b)) =
      (if φ = ψ then
        (((Real.sqrt (B : ℝ))⁻¹ : ℝ) : ℂ)
      else 0) *
        dSVUniformDensityThresholdWholeHistorySharedState
          N d L (a, b) := by
  simp [dSVDensityRationalPublicLogPhasePureSource,
    dSVDensityRationalPublicLogBilateralPureTensor, ePRState]
end QuantumParallelRepetition
