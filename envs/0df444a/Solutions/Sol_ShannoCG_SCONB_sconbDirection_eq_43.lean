-- Prove2me | solution 1 for ShannoCG.SCONB.sconbDirection_eq_43
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:28:00.62815+00:00
-- url     : https://prove2.me/submissions/4e9aa260-2b2c-43ed-b0ec-9c717f6f1c7c

import Mathlib
import Definitions.Def_ShannoCG_SCONB_sconbDirection
open Matrix ShannoCG.SCONB

private theorem bfgs_exact {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (p y g : Fin n → ℝ)
    (hexact : p ⬝ᵥ g = 0) :
    -(bfgsUpdate H p y *ᵥ g) = -(H *ᵥ g) + ((y ⬝ᵥ (H *ᵥ g)) / (p ⬝ᵥ y)) • p := by
  simp only [bfgsUpdate, add_mulVec, smul_mulVec, sub_mulVec,
    vecMulVec_mulVec, ← dotProduct_mulVec, hexact]
  ext i
  simp [smul_eq_mul, div_eq_mul_inv]
  <;> ring

private theorem scaled_orth {n : ℕ} (pt yt g : Fin n → ℝ) (hpy : pt ⬝ᵥ yt ≠ 0)
    (horth : pt ⬝ᵥ g = 0) :
    scaledRestart pt yt *ᵥ g = gammaScale pt yt • g - ((yt ⬝ᵥ g) / (yt ⬝ᵥ yt)) • pt := by
  simp only [scaledRestart, add_mulVec, smul_mulVec, sub_mulVec, one_mulVec,
    vecMulVec_mulVec, horth]
  ext i
  simp [gammaScale, smul_eq_mul]
  field_simp
  <;> ring

theorem solution {n : ℕ} (pt yt pk yk g : Fin n → ℝ) (hpy : pt ⬝ᵥ yt ≠ 0)
    (hexact_k : pk ⬝ᵥ g = 0) (horth : pt ⬝ᵥ g = 0) (hconj : yk ⬝ᵥ pt = 0) :
    sconbDirection pt yt pk yk g =
      -(gammaScale pt yt • g) + ((yt ⬝ᵥ g) / (yt ⬝ᵥ yt)) • pt
        + ((yk ⬝ᵥ g) / (pk ⬝ᵥ yk) * gammaScale pt yt) • pk := by
  rw [sconbDirection, bfgs_exact _ _ _ _ hexact_k, scaled_orth _ _ _ hpy horth]
  simp only [dotProduct_sub, dotProduct_smul, hconj, smul_zero, sub_zero]
  ext i
  simp [smul_eq_mul, div_eq_mul_inv]
  <;> ring
