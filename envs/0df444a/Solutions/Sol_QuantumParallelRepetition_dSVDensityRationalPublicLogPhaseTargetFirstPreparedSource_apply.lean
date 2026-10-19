-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/40b9ad29-b621-4699-a904-38835a9a7e57

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_dSVDensityRationalPublicLogPhaseHarmonicPureSource_apply

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
    dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource
        B N d L m
        (dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
            B N d L m ((φ, a), i),
          dSVDensityRationalPublicLogPhaseTargetFirstIndexEquiv
            B N d L m ((ψ, b), j)) =
      (if φ = ψ then
        (((Real.sqrt (B : ℝ))⁻¹ : ℝ) : ℂ)
      else 0) *
        dSVUniformDensityThresholdWholeHistorySharedState
          N d L (a, b) *
        embezzlementState m (i, j) := by
  unfold dSVDensityRationalPublicLogPhaseTargetFirstPreparedSource
  simpa [LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft'] using
    (dSVDensityRationalPublicLogPhaseHarmonicPureSource_apply
      B N d L m φ ψ a b i j)
end QuantumParallelRepetition
