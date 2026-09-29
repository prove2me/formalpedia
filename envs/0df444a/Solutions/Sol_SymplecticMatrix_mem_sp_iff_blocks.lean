-- Prove2me | solution 1 for SymplecticMatrix.mem_sp_iff_blocks
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T15:45:00.839973+00:00
-- url     : https://prove2.me/submissions/a909e8b1-cf97-4755-856d-29c1574128ee

import Definitions.Def_symplectic_block_generators

open Matrix SymplecticMatrix

theorem solution {l : ℕ} {R : Type*} [CommRing R] (a b c d : Matrix (Fin l) (Fin l) R) :
    Matrix.fromBlocks a b c d ∈ LieAlgebra.Symplectic.sp (Fin l) R ↔
      d = -a.transpose ∧ b.transpose = b ∧ c.transpose = c := by
  rw [LieAlgebra.Symplectic.sp, mem_skewAdjointMatricesLieSubalgebra,
    mem_skewAdjointMatricesSubmodule]
  show (Matrix.fromBlocks a b c d)ᵀ * Matrix.J (Fin l) R
      = Matrix.J (Fin l) R * (-(Matrix.fromBlocks a b c d)) ↔ _
  rw [Matrix.J, fromBlocks_transpose, fromBlocks_neg, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_inj]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨?_, ?_, ?_⟩ <;> simp_all
  · rintro ⟨h1, h2, h3⟩
    subst h1
    refine ⟨by simp [h3], by simp, by simp, by simp [h2]⟩
