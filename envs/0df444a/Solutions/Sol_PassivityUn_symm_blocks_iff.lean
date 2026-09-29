-- Prove2me | solution 1 for PassivityUn.symm_blocks_iff
-- status  : ACCEPTED   (prove)
-- author  : @ShapeZero
-- created : 2026-09-23T21:35:34.684497+00:00
-- url     : https://prove2.me/submissions/0368b8ac-c8d8-4100-9958-1681d7510f82

import Mathlib

open Matrix

theorem solution (n : ℕ) (A B : Matrix (Fin n) (Fin n) ℝ) :
    (Matrix.fromBlocks A (-B) B A)ᵀ = Matrix.fromBlocks A (-B) B A
      ↔ Aᵀ = A ∧ Bᵀ = -B := by
  rw [fromBlocks_transpose, fromBlocks_inj]
  constructor
  · rintro ⟨h1, h2, -, -⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; refine ⟨h1, h2, ?_, h1⟩; rw [transpose_neg, h2, neg_neg]
