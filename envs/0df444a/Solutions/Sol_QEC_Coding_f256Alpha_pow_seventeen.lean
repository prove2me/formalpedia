-- Prove2me | solution 1 for QEC.Coding.f256Alpha_pow_seventeen
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-06T11:47:52.149195+00:00
-- url     : https://prove2.me/submissions/1dde0e21-d173-446c-b059-609e186c7cbb

import Definitions.Def_QEC_Coding_FiniteFieldMultiplication_SelfDualBasis
import Mathlib.Tactic
set_option autoImplicit false
open Polynomial
open QEC QEC.Coding

private theorem f256Alpha_pow_eq_mk (k : ℕ) :
    f256Alpha ^ k = AdjoinRoot.mk f256Modulus (X ^ k) := by
  simp [f256Alpha, ← AdjoinRoot.mk_X]

theorem solution : f256Alpha ^ 17 = 1 := by
  rw [f256Alpha_pow_eq_mk, ← (AdjoinRoot.mk f256Modulus).map_one,
    AdjoinRoot.mk_eq_mk]
  refine ⟨(X + 1) * (X ^ 8 + X ^ 7 + X ^ 6 + X ^ 4 + X ^ 2 + X + 1), ?_⟩
  simp only [f256Modulus]
  ring_nf
  reduce_mod_char
