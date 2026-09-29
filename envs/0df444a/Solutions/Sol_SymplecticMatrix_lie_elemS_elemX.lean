-- Prove2me | solution 1 for SymplecticMatrix.lie_elemS_elemX
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-27T15:45:02.25162+00:00
-- url     : https://prove2.me/submissions/27195b20-188b-48ba-91c3-8e8adcd023e8

import Definitions.Def_symplectic_block_generators

open Matrix SymplecticMatrix

private lemma fb_sub {R : Type*} [CommRing R] {n m : Type*} [DecidableEq n] [DecidableEq m]
    (a a' : Matrix n n R) (b b' : Matrix n m R)
    (c c' : Matrix m n R) (d d' : Matrix m m R) :
    Matrix.fromBlocks a b c d - Matrix.fromBlocks a' b' c' d'
      = Matrix.fromBlocks (a - a') (b - b') (c - c') (d - d') := by
  ext p q; rcases p with p | p <;> rcases q with q | q <;> simp

theorem solution {l : ℕ} {R : Type*} [CommRing R] (i j : Fin l) (hij : i ≠ j) :
    ⁅(elemS i i : Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R),
      (elemX i j : Matrix (Fin l ⊕ Fin l) (Fin l ⊕ Fin l) R)⁆ = elemS i j := by
  rw [Ring.lie_def, elemS, elemS, elemX, fromBlocks_multiply, fromBlocks_multiply, fb_sub]
  simp [symmMatrix, hij, Matrix.transpose_single, add_comm]
