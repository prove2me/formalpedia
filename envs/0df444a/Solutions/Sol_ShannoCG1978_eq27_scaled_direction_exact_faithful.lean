-- Prove2me | solution 1 for ShannoCG1978.eq27_scaled_direction_exact_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T03:09:33.480974+00:00
-- url     : https://prove2.me/submissions/2eea6393-86d6-46b8-8017-a8ac5e5793d1

import Mathlib
import Definitions.Def_ShannoCG_SCONB_gammaScale
import Definitions.Def_ShannoCG_SCONB_scaledRestart

open Matrix ShannoCG.SCONB

theorem solution {n : ℕ} (p y g : Fin n → ℝ)
    (hpy : 0 < p ⬝ᵥ y) (hexact : p ⬝ᵥ g = 0) :
    -(scaledRestart p y *ᵥ g) = gammaScale p y • (-g + ((y ⬝ᵥ g) / (p ⬝ᵥ y)) • p) := by
  unfold scaledRestart
  simp only [add_mulVec, sub_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, one_mulVec, hexact]
  ext i
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]

  have : p ⬝ᵥ y ≠ 0 := hpy.ne'
  field_simp
  ring
