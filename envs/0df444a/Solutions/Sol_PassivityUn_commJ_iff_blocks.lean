-- Prove2me | solution 1 for PassivityUn.commJ_iff_blocks
-- status  : ACCEPTED   (prove)
-- author  : @ShapeZero
-- created : 2026-09-23T21:35:33.809829+00:00
-- url     : https://prove2.me/submissions/00cdbf95-0a61-45b0-b958-6a4d570c47a7

import Mathlib
import Definitions.Def_PassivityUn_stdJ

open Matrix PassivityUn

theorem solution (n : ℕ) (A B C D : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.fromBlocks A B C D * stdJ n = stdJ n * Matrix.fromBlocks A B C D
      ↔ D = A ∧ B = -C := by
  simp only [stdJ, fromBlocks_multiply, fromBlocks_inj]
  simp
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨by rw [← neg_neg D, ← h2, neg_neg], by rw [h1]⟩
  · rintro ⟨rfl, rfl⟩; simp
