-- Prove2me | solution 1 for QuantumParallelRepetition.purificationRangeProjection_compression
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/f1ea619a-da7a-45e3-b9a5-1669a100f5ea

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_mul_spectralSupportInverse
import Theorems.Thm_QuantumParallelRepetition_spectralSupportProjection_mul

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 400000
namespace QuantumParallelRepetition
theorem _root_.solution
    {d e : Type*} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F) :
    Matrix.conjTranspose Γ * purificationRangeProjection F hF Γ * Γ = F := by
  unfold purificationRangeProjection
  calc
    Matrix.conjTranspose Γ *
        (Γ * spectralSupportInverse F hF * Matrix.conjTranspose Γ) * Γ =
      (Matrix.conjTranspose Γ * Γ) * spectralSupportInverse F hF *
        (Matrix.conjTranspose Γ * Γ) := by
          simp only [Matrix.mul_assoc]
    _ = F * spectralSupportInverse F hF * F := by rw [hΓ]
    _ = spectralSupportProjection F hF * F := by
      rw [mul_spectralSupportInverse]
    _ = F := spectralSupportProjection_mul F hF
end QuantumParallelRepetition
