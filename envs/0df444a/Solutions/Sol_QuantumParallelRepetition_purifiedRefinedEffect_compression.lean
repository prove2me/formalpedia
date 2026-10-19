-- Prove2me | solution 1 for QuantumParallelRepetition.purifiedRefinedEffect_compression
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/abf28e1d-f502-4992-ad02-9d33eee0a501

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_purificationRangeProjection_complement_compression
import Theorems.Thm_QuantumParallelRepetition_purifiedRefinementCore_compression

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
set_option maxHeartbeats 400000
namespace QuantumParallelRepetition
theorem _root_.solution
    {ι d e : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (F : Matrix d d ℂ) (hF : F.PosSemidef)
    (Γ : Matrix e d ℂ)
    (hΓ : Matrix.conjTranspose Γ * Γ = F)
    (effect : ι → Matrix d d ℂ)
    (hpositive : ∀ a, (effect a).PosSemidef)
    (hsum : (∑ a : ι, effect a) = F)
    (a₀ a : ι) :
    Matrix.conjTranspose Γ *
        purifiedRefinedEffect F hF Γ effect a₀ a * Γ = effect a := by
  have hdefect : Matrix.conjTranspose Γ *
      (if a = a₀ then 1 - purificationRangeProjection F hF Γ else 0) *
        Γ = 0 := by
    split
    · exact purificationRangeProjection_complement_compression F hF Γ hΓ
    · simp
  change Matrix.conjTranspose Γ *
      (purifiedRefinementCore F hF Γ effect a +
        if a = a₀ then 1 - purificationRangeProjection F hF Γ else 0) *
        Γ = effect a
  rw [Matrix.mul_add, Matrix.add_mul]
  rw [purifiedRefinementCore_compression F hF Γ hΓ
    effect hpositive hsum a, hdefect, add_zero]
end QuantumParallelRepetition
