-- Prove2me | solution 1 for QuantumParallelRepetition.dSVDensityRationalPublicLogPhasePhysicalHistoryUnitary_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:15.231807+00:00
-- url     : https://prove2.me/submissions/be73d499-6c1a-4faf-88b5-a9e5029dc9e0

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
open scoped ComplexOrder Matrix BigOperators InnerProductSpace
open Complex Matrix Finset
noncomputable section
open WithLp
open scoped BigOperators ComplexOrder Kronecker MatrixOrder
namespace QuantumParallelRepetition
theorem _root_.solution
    (B : ℕ) {N d L : ℕ}
    (U : Matrix.unitaryGroup
      (DSVUniformDensityThresholdWholeHistoryLocalIndex
        N d L) ℂ)
    (φ ψ : Fin B)
    (a b : DSVUniformDensityThresholdWholeHistoryLocalIndex
      N d L) :
    dSVDensityRationalPublicLogPhasePhysicalHistoryUnitary
        B U (φ, a) (ψ, b) =
      if φ = ψ then U a b else 0 := by
  classical
  change
    ((1 : Matrix (Fin B) (Fin B) ℂ) ⊗ₖ U.val)
      (φ, a) (ψ, b) = _
  simp [Matrix.kroneckerMap_apply, Matrix.one_apply]
end QuantumParallelRepetition
