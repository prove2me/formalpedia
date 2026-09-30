-- Prove2me | solution 1 for ShannoCG.SCONB.bfgsUpdate_mulVec_of_exact
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:26:52.206904+00:00
-- url     : https://prove2.me/submissions/717416ba-0010-4a88-bd15-2f9414f3c1ac

import Mathlib
import Definitions.Def_ShannoCG_SCONB_sconbDirection
open Matrix ShannoCG.SCONB

theorem solution {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (p y g : Fin n → ℝ)
    (hexact : p ⬝ᵥ g = 0) :
    -(bfgsUpdate H p y *ᵥ g) = -(H *ᵥ g) + ((y ⬝ᵥ (H *ᵥ g)) / (p ⬝ᵥ y)) • p := by
  simp only [bfgsUpdate, add_mulVec, smul_mulVec, sub_mulVec,
    vecMulVec_mulVec, ← dotProduct_mulVec, hexact]
  ext i
  simp [smul_eq_mul, div_eq_mul_inv]
  <;> ring
