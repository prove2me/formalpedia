-- Prove2me | solution 1 for QuantumParallelRepetition.purifiedRefinementCore_compression
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/c0b93465-c58f-48f2-90af-59df1b0968a0

import Mathlib
import Definitions.Def_QuantumParallelRepetition
import Theorems.Thm_QuantumParallelRepetition_spectralSupportInverse_mul
import Theorems.Thm_QuantumParallelRepetition_mul_spectralSupportInverse
import Theorems.Thm_QuantumParallelRepetition_posSemidef_mul_spectralSupportProjection
import Theorems.Thm_QuantumParallelRepetition_spectralSupportProjection_mul_posSemidef
import Theorems.Thm_QuantumParallelRepetition_refinement_complement_posSemidef

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
    (a : ι) :
    Matrix.conjTranspose Γ *
        purifiedRefinementCore F hF Γ effect a * Γ = effect a := by
  have hsub : (F - effect a).PosSemidef := by
    rw [← hsum]
    exact refinement_complement_posSemidef effect hpositive a
  unfold purifiedRefinementCore
  calc
    Matrix.conjTranspose Γ *
        (Γ * spectralSupportInverse F hF * effect a *
          spectralSupportInverse F hF * Matrix.conjTranspose Γ) * Γ =
      (Matrix.conjTranspose Γ * Γ) * spectralSupportInverse F hF *
        effect a * spectralSupportInverse F hF *
          (Matrix.conjTranspose Γ * Γ) := by
            simp only [Matrix.mul_assoc]
    _ = F * spectralSupportInverse F hF * effect a *
          spectralSupportInverse F hF * F := by
            rw [hΓ]
    _ = (F * spectralSupportInverse F hF) * effect a *
          (spectralSupportInverse F hF * F) := by
            simp only [Matrix.mul_assoc]
    _ = spectralSupportProjection F hF * effect a *
          spectralSupportProjection F hF := by
            rw [mul_spectralSupportInverse, spectralSupportInverse_mul]
    _ = effect a := by
      rw [spectralSupportProjection_mul_posSemidef hF
        (hpositive a) hsub]
      exact posSemidef_mul_spectralSupportProjection hF
        (hpositive a) hsub
end QuantumParallelRepetition
