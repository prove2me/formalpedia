-- Prove2me | solution 1 for QuantumParallelRepetition.purificationRangeProjection_complement_compression
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/ffb2ca01-3075-430b-b130-76fa845af01e

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_purificationRangeProjection_compression

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
    Matrix.conjTranspose Γ *
        (1 - purificationRangeProjection F hF Γ) * Γ = 0 := by
  calc
    Matrix.conjTranspose Γ *
        (1 - purificationRangeProjection F hF Γ) * Γ =
      Matrix.conjTranspose Γ * Γ -
        Matrix.conjTranspose Γ * purificationRangeProjection F hF Γ * Γ := by
          rw [Matrix.mul_sub, Matrix.sub_mul]
          simp
    _ = F - F := by
      rw [hΓ, purificationRangeProjection_compression F hF Γ hΓ]
    _ = 0 := sub_self F
end QuantumParallelRepetition
