-- Prove2me | solution 1 for SpectralBounds.exists_quadForm_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T12:19:23.80554+00:00
-- url     : https://prove2.me/submissions/9eaa7f2e-514e-4999-b630-69f44e435d77

module
public import Mathlib
public import Definitions.Def_SpectralLib_SpectralBounds

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open SpectralBounds
variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V)
  [DecidableRel G.Adj] (hA : (G.adjMatrix ℝ).IsHermitian)
variable {W : Type*} [Fintype W] [DecidableEq W] {M : Matrix W W ℝ}
open Matrix
namespace SpectralBounds
theorem _root_.solution (hM : M.IsHermitian) (x : W → ℝ) :
    ∃ y : W → ℝ, x ⬝ᵥ (M *ᵥ x) = ∑ i, hM.eigenvalues i * y i ^ 2 ∧
      x ⬝ᵥ x = ∑ i, y i ^ 2 := by
  set U : Matrix W W ℝ := (hM.eigenvectorUnitary : Matrix W W ℝ) with hU
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self _
  have hs : star U = Uᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  refine ⟨Uᵀ *ᵥ x, ?_, ?_⟩
  · conv_lhs => rw [hM.spectral_theorem]
    simp only [Unitary.conjStarAlgAut_apply]
    rw [← hU, hs, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose]
    simp [dotProduct, mulVec_diagonal, sq, mul_left_comm]
  · have : ∑ i, (Uᵀ *ᵥ x) i ^ 2 = (Uᵀ *ᵥ x) ⬝ᵥ (Uᵀ *ᵥ x) := by simp [dotProduct, sq]
    rw [this, dotProduct_mulVec, vecMul_transpose, mulVec_mulVec, ← hs, hUU, one_mulVec,
      dotProduct_comm]
end SpectralBounds
