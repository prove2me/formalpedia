-- Prove2me | solution 1 for ShannoCG1978.eq20_memoryless_bfgs_direction_faithful
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T03:08:22.829755+00:00
-- url     : https://prove2.me/submissions/efbd1631-d9a1-4dc9-bd39-fbf0152ed52f

import Mathlib
import Definitions.Def_ShannoCG_SCONB_bfgsUpdate

open Matrix ShannoCG.SCONB

theorem solution {n : ℕ} (p y g : Fin n → ℝ)
    (hpy : 0 < p ⬝ᵥ y) :
    -(bfgsUpdate (1 : Matrix (Fin n) (Fin n) ℝ) p y *ᵥ g) =
      -g - ((1 + (y ⬝ᵥ y) / (p ⬝ᵥ y)) * ((p ⬝ᵥ g) / (p ⬝ᵥ y)) - (y ⬝ᵥ g) / (p ⬝ᵥ y)) • p
        + ((p ⬝ᵥ g) / (p ⬝ᵥ y)) • y := by
  unfold bfgsUpdate
  simp only [add_mulVec, sub_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, one_mulVec, vecMul_one]
  ext i
  simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  have : p ⬝ᵥ y ≠ 0 := hpy.ne'
  field_simp
  ring
