-- Prove2me | solution 1 for RobustSDP.Uniqueness.schur_reformulation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T22:37:11.05241+00:00
-- url     : https://prove2.me/submissions/b46c26a1-40f4-4385-8cb1-02737ee22820

import Mathlib
import Definitions.Def_RobustSDP_Uniqueness_Model
import Definitions.Def_RobustSDP_Uniqueness_Hypotheses

open Matrix RobustSDP.Uniqueness

theorem solution {m n p q : ℕ} (D : SDPData m n p q) (x : Fin m → ℝ) (τ : ℝ)
    (hτ : 0 < τ) :
    D.Feasible (x, τ) ↔ (D.G (x, τ)).PosSemidef := by
  have hτne : τ ≠ 0 := ne_of_gt hτ
  have hEmul' :
      (τ • (1 : Matrix (Fin q) (Fin q) ℝ)) * (τ⁻¹ • (1 : Matrix (Fin q) (Fin q) ℝ)) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul, mul_inv_cancel₀ hτne, one_smul]
  have hEmul :
      (τ⁻¹ • (1 : Matrix (Fin q) (Fin q) ℝ)) * (τ • (1 : Matrix (Fin q) (Fin q) ℝ)) = 1 := by
    rw [Matrix.smul_mul, Matrix.mul_smul, one_mul, smul_smul, inv_mul_cancel₀ hτne, one_smul]
  letI : Invertible (τ • (1 : Matrix (Fin q) (Fin q) ℝ)) :=
    ⟨τ⁻¹ • (1 : Matrix (Fin q) (Fin q) ℝ), hEmul, hEmul'⟩
  have hEinv : (τ • (1 : Matrix (Fin q) (Fin q) ℝ))⁻¹
      = τ⁻¹ • (1 : Matrix (Fin q) (Fin q) ℝ) := Matrix.inv_eq_right_inv hEmul'
  have hEpd : (τ • (1 : Matrix (Fin q) (Fin q) ℝ)).PosDef := Matrix.PosDef.one.smul hτ
  have hBH : ((D.R x)ᵀ)ᴴ = D.R x := by
    ext i j
    simp
  have hschur := Matrix.PosDef.fromBlocks₂₂ (D.F x - τ • (D.L * D.Lᵀ)) ((D.R x)ᵀ) hEpd
  rw [hBH] at hschur
  have hlmi : D.lmi x τ = fromBlocks (D.F x - τ • (D.L * D.Lᵀ)) ((D.R x)ᵀ) (D.R x)
      (τ • (1 : Matrix (Fin q) (Fin q) ℝ)) := rfl
  have hGeq : (D.F x - τ • (D.L * D.Lᵀ))
      - (D.R x)ᵀ * (τ • (1 : Matrix (Fin q) (Fin q) ℝ))⁻¹ * (D.R x) = D.G (x, τ) := by
    rw [hEinv, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    rfl
  show (D.lmi x τ).PosSemidef ↔ (D.G (x, τ)).PosSemidef
  rw [hlmi, hschur, hGeq]
