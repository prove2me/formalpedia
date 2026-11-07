-- Prove2me | solution 1 for QEC.Coding.f256Alpha_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-06T11:50:12.902728+00:00
-- url     : https://prove2.me/submissions/15328254-c03a-409b-97cb-9cd53cb39469

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Mathlib.Tactic
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding
theorem solution : f256Alpha ≠ 1 := by
  intro h
  have hroot := AdjoinRoot.eval₂_root f256Modulus
  have h' : AdjoinRoot.root f256Modulus = 1 := by simpa [f256Alpha] using h
  rw [h'] at hroot
  norm_num [f256Modulus, eval₂_add, eval₂_pow, eval₂_X, eval₂_one, eval₂_C] at hroot
  exact (by norm_num : ¬ 2 ∣ 5) ((CharP.cast_eq_zero_iff F256 2 5).mp hroot)
