-- Prove2me | solution 1 for PI.SqPair.LocCartanPairW.cmp_block_of_gram
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:23:07.579016+00:00
-- url     : https://prove2.me/submissions/cd821c59-d47f-491f-8a9c-2e802ae9728e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalCartanPairs_CmpBlock

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.SqPair PI.SqPair.LocCartanPairW
variable {R : Type*} [CommRing R] (σ : R ≃+* R)
namespace PI.SqPair.LocCartanPairW
theorem _root_.solution [IsDomain R] {μ κ : Type*} [Fintype μ] [Fintype κ] [DecidableEq μ]
    (M : Matrix (μ ⊕ κ) (μ ⊕ κ) R) (J : Matrix μ μ R) (A₁ A₁' : Matrix κ κ R) (s : R)
    (hM : (M.map σ)ᵀ * fromBlocks J 0 0 A₁ * M = s • fromBlocks J 0 0 A₁')
    (h21 : M.toBlocks₂₁ = 0)
    (hdet : (((M.toBlocks₁₁).map σ)ᵀ * J).det ≠ 0) :
    M.toBlocks₁₂ = 0 ∧ ((M.toBlocks₂₂).map σ)ᵀ * A₁ * M.toBlocks₂₂ = s • A₁' := by
  have hM' := hM
  rw [← Matrix.fromBlocks_toBlocks M, h21] at hM'
  simp only [Matrix.fromBlocks_map, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_smul, Matrix.map_zero _ (map_zero σ), Matrix.transpose_zero,
    Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, smul_zero] at hM'
  obtain ⟨-, h12', -, h22'⟩ := Matrix.fromBlocks_inj.1 hM'
  have hQ : M.toBlocks₁₂ = 0 := by
    have h1 : (((M.toBlocks₁₁).map σ)ᵀ * J).adjugate *
        (((M.toBlocks₁₁).map σ)ᵀ * J * M.toBlocks₁₂) = 0 := by
      rw [h12', Matrix.mul_zero]
    rw [← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul] at h1
    ext i j
    have hij := congrArg (fun X => X i j) h1
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at hij
    exact (mul_eq_zero.1 hij).resolve_left hdet
  refine ⟨hQ, ?_⟩
  rw [hQ] at h22'
  simpa using h22'
end PI.SqPair.LocCartanPairW
