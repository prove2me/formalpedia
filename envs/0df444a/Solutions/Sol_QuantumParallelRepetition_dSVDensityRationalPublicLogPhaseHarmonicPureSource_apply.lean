-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalPublicLogPhaseHarmonicPureSource_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/1d7a5825-986c-4f89-aa86-de751739b082

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalPublicLogPhasePureSource_apply

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
    (B N d L m : ℕ)
    (φ ψ : Fin B)
    (a b : DSVUniformDensityThresholdWholeHistoryLocalIndex
      N d L) (i j : Fin m) :
    dSVDensityRationalPublicLogPhaseHarmonicPureSource
        B N d L m (((φ, a), i), ((ψ, b), j)) =
      (if φ = ψ then
        (((Real.sqrt (B : ℝ))⁻¹ : ℝ) : ℂ)
      else 0) *
        dSVUniformDensityThresholdWholeHistorySharedState
          N d L (a, b) *
        embezzlementState m (i, j) := by
  change
    dSVDensityRationalPublicLogPhasePureSource
        B N d L ((φ, a), (ψ, b)) *
      embezzlementState m (i, j) = _
  rw [dSVDensityRationalPublicLogPhasePureSource_apply]
end QuantumParallelRepetition
