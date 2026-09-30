-- Prove2me | solution 1 for ShannoCG.SCONB.scaledRestart_mulVec_of_orth
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:15:59.081857+00:00
-- url     : https://prove2.me/submissions/aeb0f9ed-5fd3-41e5-bcdf-1602f29bc38b

import Mathlib
import Definitions.Def_ShannoCG_SCONB_scaledRestart
open Matrix ShannoCG.SCONB

theorem solution {n : ℕ} (pt yt g : Fin n → ℝ) (hpy : pt ⬝ᵥ yt ≠ 0)
    (horth : pt ⬝ᵥ g = 0) :
    scaledRestart pt yt *ᵥ g = gammaScale pt yt • g - ((yt ⬝ᵥ g) / (yt ⬝ᵥ yt)) • pt := by
  simp only [scaledRestart, add_mulVec, smul_mulVec, sub_mulVec, one_mulVec,
    vecMulVec_mulVec, horth]
  ext i
  simp [gammaScale, smul_eq_mul]
  field_simp
  <;> ring
