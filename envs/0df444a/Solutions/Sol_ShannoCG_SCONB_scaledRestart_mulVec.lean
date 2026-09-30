-- Prove2me | solution 1 for ShannoCG.SCONB.scaledRestart_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:26:51.474792+00:00
-- url     : https://prove2.me/submissions/d23c878e-252d-4fba-8e4e-69de1fbd6b7e

import Mathlib
import Definitions.Def_ShannoCG_SCONB_sconbDirection
open Matrix ShannoCG.SCONB

theorem solution {n : ℕ} (pt yt g : Fin n → ℝ) (hpy : pt ⬝ᵥ yt ≠ 0) :
    scaledRestart pt yt *ᵥ g =
      gammaScale pt yt • g - ((pt ⬝ᵥ g) / (yt ⬝ᵥ yt)) • yt
        + (2 * ((pt ⬝ᵥ g) / (pt ⬝ᵥ yt)) - (yt ⬝ᵥ g) / (yt ⬝ᵥ yt)) • pt := by
  have hyy : yt ⬝ᵥ yt ≠ 0 := by
    intro h
    have hy : yt = 0 := dotProduct_self_eq_zero.mp h
    subst yt
    simp at hpy
  simp only [scaledRestart, add_mulVec, smul_mulVec, sub_mulVec, one_mulVec,
    vecMulVec_mulVec]
  ext i
  simp [gammaScale, smul_eq_mul]
  field_simp
  <;> ring
