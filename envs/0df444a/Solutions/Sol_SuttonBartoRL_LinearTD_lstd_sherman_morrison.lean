-- Prove2me | solution 1 for SuttonBartoRL.LinearTD.lstd_sherman_morrison
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:31:08.226613+00:00
-- url     : https://prove2.me/submissions/702f036e-1691-4759-947f-294490a5307b

import Mathlib
import Definitions.Def_SuttonBartoRL_LinearTD_MDP
import Definitions.Def_SuttonBartoRL_LinearTD_LinearTD

set_option autoImplicit false

open Matrix

lemma sm9e2b_vmv_smul {d : ℕ} (u v : Fin d → ℝ) (s : ℝ) :
    vecMulVec u (s • v) = s • vecMulVec u v := by
  ext i j
  simp [vecMulVec_apply]
  ring

lemma sm9e2b_key {d : ℕ} (M : Matrix (Fin d) (Fin d) ℝ) (u v : Fin d → ℝ) :
    vecMulVec u v * M * vecMulVec u v = (v ⬝ᵥ (M *ᵥ u)) • vecMulVec u v := by
  rw [Matrix.mul_assoc, mul_vecMulVec, vecMulVec_mul_vecMulVec, sm9e2b_vmv_smul]

lemma sm9e2b_right_inv {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (u v : Fin d → ℝ)
    (hinv : IsUnit A.det) (hden : 1 + v ⬝ᵥ (A⁻¹ *ᵥ u) ≠ 0) :
    (A + vecMulVec u v) *
      (A⁻¹ - (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))⁻¹ • (A⁻¹ * vecMulVec u v * A⁻¹)) = 1 := by
  set c := 1 + v ⬝ᵥ (A⁻¹ *ᵥ u) with hc
  have hAA : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hinv
  have hk : vecMulVec u v * A⁻¹ * vecMulVec u v * A⁻¹
      = (v ⬝ᵥ (A⁻¹ *ᵥ u)) • (vecMulVec u v * A⁻¹) := by
    rw [sm9e2b_key, Matrix.smul_mul]
  have e1 : A * (A⁻¹ * vecMulVec u v * A⁻¹) = vecMulVec u v * A⁻¹ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hAA, Matrix.one_mul]
  have e2 : vecMulVec u v * (A⁻¹ * vecMulVec u v * A⁻¹)
      = (v ⬝ᵥ (A⁻¹ *ᵥ u)) • (vecMulVec u v * A⁻¹) := by
    rw [← hk]; simp only [Matrix.mul_assoc]
  rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_smul, e1, e2,
    hAA, smul_smul]
  have hs : v ⬝ᵥ (A⁻¹ *ᵥ u) = c - 1 := by rw [hc]; ring
  rw [hs]
  have : c⁻¹ * (c - 1) = 1 - c⁻¹ := by field_simp
  rw [this, sub_smul, one_smul]
  abel

open Matrix SuttonBartoRL.LinearTD in
theorem solution {d : ℕ} (γ ε : ℝ) (x : ℕ → Fin d → ℝ) (t : ℕ)
    (hinv : IsUnit (lstdA γ ε x t).det)
    (hden : 1 + (x t - γ • x (t + 1)) ⬝ᵥ ((lstdA γ ε x t)⁻¹ *ᵥ x t) ≠ 0) :
    lstdA γ ε x (t + 1) = lstdA γ ε x t + vecMulVec (x t) (x t - γ • x (t + 1)) ∧
      IsUnit (lstdA γ ε x (t + 1)).det ∧
      (lstdA γ ε x (t + 1))⁻¹ =
        (lstdA γ ε x t)⁻¹ -
          (1 + (x t - γ • x (t + 1)) ⬝ᵥ ((lstdA γ ε x t)⁻¹ *ᵥ x t))⁻¹ •
            ((lstdA γ ε x t)⁻¹ * vecMulVec (x t) (x t - γ • x (t + 1)) * (lstdA γ ε x t)⁻¹) := by
  have h1 : lstdA γ ε x (t + 1) = lstdA γ ε x t + vecMulVec (x t) (x t - γ • x (t + 1)) := by
    unfold lstdA
    rw [Finset.sum_range_succ]
    abel
  have hR := sm9e2b_right_inv (lstdA γ ε x t) (x t) (x t - γ • x (t + 1)) hinv hden
  rw [← h1] at hR
  refine ⟨h1, Matrix.isUnit_det_of_right_inverse hR, Matrix.inv_eq_right_inv hR⟩
