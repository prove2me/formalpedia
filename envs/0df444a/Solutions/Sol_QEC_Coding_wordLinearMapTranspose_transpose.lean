-- Prove2me | solution 1 for QEC.Coding.wordLinearMapTranspose_transpose
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:36:52.898713+00:00
-- url     : https://prove2.me/submissions/c2fc89b3-5fb3-4e2f-b52f-15c9b4282cb4

import Definitions.Def_QEC_Coding_ChainComplex_HomotopyDistance
import Definitions.Def_QEC_Coding_ChainComplex_Duality
set_option autoImplicit false
open QEC QEC.Coding
universe u v
variable {F : Type u} [Field F] [Fintype F] [DecidableEq F]
variable {i0 i1 i2 : Type v}
variable [Fintype i0] [Fintype i1] [Fintype i2]

theorem solution
    (f : Word F i0 →ₗ[F] Word F i1) :
    wordLinearMapTranspose (wordLinearMapTranspose f) = f := by
  apply LinearMap.ext
  intro x
  rw [← sub_eq_zero]
  apply (wordPairing_nondegenerate (F := F) (ι := i1)).left
  intro y
  simp only [map_sub, LinearMap.sub_apply]
  rw [wordPairing_wordLinearMapTranspose]
  rw [wordPairing_apply, dotProduct_comm]
  rw [← wordPairing_apply]
  rw [wordPairing_wordLinearMapTranspose]
  simp [wordPairing_apply, dotProduct_comm]
