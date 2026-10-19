-- Prove2me | solution 1 for QuantumParallelRepetition.unconditionalActualOneScaleFlagControlledFiniteStageDecoder_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:17.846829+00:00
-- url     : https://prove2.me/submissions/7b00bd39-1370-4456-9c07-8d655d2d5b81

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
attribute [local instance] Classical.propDecidable
namespace QuantumParallelRepetition
theorem _root_.solution
    {S B N d L m : ℕ} {R : Type}
    [Fintype R] [DecidableEq R]
    (phaseSplit :
      DSVDensityRationalPublicMultiscalePhaseIndex S B ≃
        Fin B × R)
    (Q : ℕ) (width : Fin S → ℝ)
    (schedule : Fin L → Fin S)
    (ξ : BipartiteUnitVector d)
    (spectral : Matrix.unitaryGroup
      (DSVUniformDensityThresholdLocalIndex N d) ℂ)
    (A : Fin B → Option ℕ → Matrix.unitaryGroup (Fin (N * m)) ℂ) :
    unconditionalSourceFlagControlledFiniteStageDecoder
        phaseSplit Q width schedule ξ spectral A =
      unconditionalActualCleanedSelectedFiniteStageDecoder
        phaseSplit Q width schedule ξ spectral A := by
  rfl
end QuantumParallelRepetition
