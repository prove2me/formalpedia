-- Prove2me | solution 1 for ShannoCG.SCONB.bfgsUpdate_mulVec_expansion
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:26:52.82862+00:00
-- url     : https://prove2.me/submissions/d3f715e6-9048-459a-bf81-589516039990

import Mathlib
import Definitions.Def_ShannoCG_SCONB_sconbDirection
open Matrix ShannoCG.SCONB

theorem solution {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (p y g : Fin n → ℝ) :
    -(bfgsUpdate H p y *ᵥ g) =
      -(H *ᵥ g) + ((p ⬝ᵥ g) / (p ⬝ᵥ y)) • (H *ᵥ y)
        - ((1 + (y ⬝ᵥ (H *ᵥ y)) / (p ⬝ᵥ y)) * ((p ⬝ᵥ g) / (p ⬝ᵥ y))
            - (y ⬝ᵥ (H *ᵥ g)) / (p ⬝ᵥ y)) • p := by
  simp only [bfgsUpdate, add_mulVec, smul_mulVec, sub_mulVec,
    vecMulVec_mulVec, ← dotProduct_mulVec]
  ext i
  simp [smul_eq_mul, div_eq_mul_inv]
  <;> ring
