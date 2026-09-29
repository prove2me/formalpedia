-- Prove2me | solution 1 for UpperHalfPlane.sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_fricke_heckeU
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/80cdc087-f0f5-544c-8b75-caaaf6dc7196

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_UpperHalfPlane_sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_fricke_heckeU

set_option autoImplicit false

open UpperHalfPlane ModularForm
open scoped MatrixGroups ModularForm

noncomputable section

namespace ALTraceIdentity

def frickeGL (M : ℕ) (hM : M ≠ 0) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(0 : ℝ), -1; (M : ℝ), 0]
    (by rw [Matrix.det_fin_two_of]; simp [hM])

@[scoped simp] theorem val_frickeGL (M : ℕ) (hM : M ≠ 0) :
    ((frickeGL M hM : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(0 : ℝ), -1; (M : ℝ), 0] := rfl

theorem det_frickeGL_pos (M : ℕ) (hM : M ≠ 0) : 0 < ((frickeGL M hM).det : ℝ) := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, val_frickeGL, Matrix.det_fin_two_of]
  have : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero hM
  linarith

theorem coe_frickeGL_smul (M : ℕ) (hM : M ≠ 0) (τ : ℍ) :
    (↑(frickeGL M hM • τ) : ℂ) = -1 / ((M : ℂ) * (τ : ℂ)) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (det_frickeGL_pos M hM)]
  simp only [UpperHalfPlane.num, UpperHalfPlane.denom, val_frickeGL, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    Complex.ofReal_zero, zero_mul, zero_add, Complex.ofReal_neg, Complex.ofReal_one,
    Complex.ofReal_natCast, add_zero]

theorem coe_beta (m : ℤ) :
    ((ModularGroup.S * ModularGroup.T ^ m * ModularGroup.S⁻¹ : SL(2, ℤ)) :
      Matrix (Fin 2) (Fin 2) ℤ) = !![1, 0; -m, 1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ModularGroup.coe_T_zpow, ModularGroup.coe_S, Matrix.SpecialLinearGroup.coe_inv,
    ModularGroup.coe_S]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem beta_apply (m : ℤ) (i j : Fin 2) :
    (ModularGroup.S * ModularGroup.T ^ m * ModularGroup.S⁻¹ : SL(2, ℤ)) i j = !![1, 0; -m, 1] i j := by
  rw [← coe_beta]

theorem coe_beta_smul (m : ℤ) (τ : ℍ) :
    (((ModularGroup.S * ModularGroup.T ^ m * ModularGroup.S⁻¹ : SL(2, ℤ)) • τ : ℍ) : ℂ)
      = (τ : ℂ) / (1 - (m : ℂ) * (τ : ℂ)) := by
  rw [UpperHalfPlane.specialLinearGroup_apply]
  simp only [beta_apply, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one]
  simp only [algebraMap_int_eq, eq_intCast, Int.cast_one, Complex.ofReal_one, one_mul,
    Int.cast_zero, Complex.ofReal_zero, add_zero, Int.cast_neg, Complex.ofReal_neg,
    Complex.ofReal_intCast]
  ring_nf

theorem slash_beta_apply (k : ℤ) (G : ℍ → ℂ) (m : ℤ) (τ : ℍ) :
    (G ∣[k] (ModularGroup.S * ModularGroup.T ^ m * ModularGroup.S⁻¹ : SL(2, ℤ))) τ
      = G ((ModularGroup.S * ModularGroup.T ^ m * ModularGroup.S⁻¹ : SL(2, ℤ)) • τ)
          * (1 - (m : ℂ) * (τ : ℂ)) ^ (-k) := by
  rw [ModularForm.SL_slash_apply, ModularGroup.denom_apply, beta_apply, beta_apply]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Int.cast_neg, Int.cast_one]
  ring_nf

theorem main (N : ℕ) [NeZero N] (k : ℤ) {q : ℕ} (hq : q ≠ 0) (hqN : q ∣ N)
    (G H V : ℍ → ℂ)
    (hGH : ∀ τ τ' : ℍ, (τ' : ℂ) * ((N : ℂ) * (τ : ℂ)) = -1 → G τ' = (τ : ℂ) ^ k * H τ)
    (hUV : ∀ τ τ' : ℍ, (τ' : ℂ) * ((N : ℂ) * (τ : ℂ)) = -1 →
      heckeU k q H τ' = (τ : ℂ) ^ k * V τ)
    (τ : ℍ) :
    ∑ j ∈ Finset.range q,
        (G ∣[k] (ModularGroup.S * ModularGroup.T ^ ((j : ℤ) * (N / q : ℕ)) * ModularGroup.S⁻¹ :
          SL(2, ℤ))) τ
      = (q : ℂ) ^ (1 - k) * (-(N : ℂ)) ^ (-k) * V (heckeMatrix q 0 • τ) := by

  set N' : ℕ := N / q with hN'def
  have hNq : N' * q = N := Nat.div_mul_cancel hqN
  have hN0 : N ≠ 0 := NeZero.ne N
  have hN'0 : N' ≠ 0 := by
    intro h; apply hN0; rw [← hNq, h, zero_mul]
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN0
  have hN'C : (N' : ℂ) ≠ 0 := by exact_mod_cast hN'0
  have hNC' : (N : ℂ) = (N' : ℂ) * (q : ℂ) := by exact_mod_cast hNq.symm
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ

  set τ₁ : ℍ := frickeGL N' hN'0 • τ with hτ₁def
  have hτ₁ : (τ₁ : ℂ) = -1 / ((N' : ℂ) * (τ : ℂ)) := coe_frickeGL_smul N' hN'0 τ

  have hterm : ∀ j : ℕ,
      (G ∣[k] (ModularGroup.S * ModularGroup.T ^ ((j : ℤ) * (N' : ℕ)) * ModularGroup.S⁻¹ :
          SL(2, ℤ))) τ
        = (-(N : ℂ) * (τ : ℂ)) ^ (-k) * H (heckeMatrix q j • τ₁) := by
    intro j
    set τ₂ : ℍ := heckeMatrix q j • τ₁ with hτ₂def
    have hτ₂ : (τ₂ : ℂ) = ((τ₁ : ℂ) + j) / q := coe_heckeMatrix_smul hq j τ₁
    have hτ₂' : (τ₂ : ℂ) = ((j : ℂ) * (N' : ℂ) * (τ : ℂ) - 1) / ((N : ℂ) * (τ : ℂ)) := by
      rw [hτ₂, hτ₁, hNC']; field_simp; ring
    have hτ₂ne : (τ₂ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ₂

    have hden : (1 - (((j : ℤ) * (N' : ℕ) : ℤ) : ℂ) * (τ : ℂ)) = -(N : ℂ) * (τ : ℂ) * (τ₂ : ℂ) := by
      rw [hτ₂']; push_cast; field_simp; ring
    have hden_ne : (1 - (((j : ℤ) * (N' : ℕ) : ℤ) : ℂ) * (τ : ℂ)) ≠ 0 := by
      rw [hden]; exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr hNC) hτ) hτ₂ne

    set τ' : ℍ := (ModularGroup.S * ModularGroup.T ^ ((j : ℤ) * (N' : ℕ)) * ModularGroup.S⁻¹ :
      SL(2, ℤ)) • τ with hτ'def
    have hτ' : (τ' : ℂ) = (τ : ℂ) / (1 - (((j : ℤ) * (N' : ℕ) : ℤ) : ℂ) * (τ : ℂ)) :=
      coe_beta_smul _ τ
    have hrel : (τ' : ℂ) * ((N : ℂ) * (τ₂ : ℂ)) = -1 := by
      rw [hτ', hden]; field_simp
    rw [slash_beta_apply, hGH τ₂ τ' hrel, hden, mul_zpow, zpow_neg (τ₂ : ℂ) k]
    have hτ₂k : (τ₂ : ℂ) ^ k ≠ 0 := zpow_ne_zero k hτ₂ne
    field_simp
  simp_rw [hterm]
  rw [← Finset.mul_sum]

  have hU : ∑ j ∈ Finset.range q, H (heckeMatrix q j • τ₁) = (q : ℂ) * heckeU k q H τ₁ := by
    rw [heckeU_apply k hq, ← mul_assoc, mul_inv_cancel₀ hqC, one_mul]
  rw [hU]

  set σ : ℍ := heckeMatrix q 0 • τ with hσdef
  have hσ : (σ : ℂ) = (τ : ℂ) / q := by
    rw [hσdef, coe_heckeMatrix_smul hq 0 τ]; push_cast; ring
  have hrel₁ : (τ₁ : ℂ) * ((N : ℂ) * (σ : ℂ)) = -1 := by
    rw [hτ₁, hσ, hNC']; field_simp
  rw [hUV σ τ₁ hrel₁, hσ, div_zpow, mul_zpow]

  have hτk : (τ : ℂ) ^ k ≠ 0 := zpow_ne_zero k hτ
  have hqk : (q : ℂ) ^ k ≠ 0 := zpow_ne_zero k hqC
  rw [zpow_sub₀ hqC, zpow_one, zpow_neg (τ : ℂ)]
  field_simp

end ALTraceIdentity
p2m_reactivate "P2MW.S_UpperHalfPlane_sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_fricke_heckeU.ALTraceIdentity"

end
p2m_reactivate "P2MW.S_UpperHalfPlane_sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_fricke_heckeU.ALTraceIdentity"

open scoped MatrixGroups ModularForm in
theorem solution (N : ℕ) [NeZero N] (k : ℤ) {q : ℕ} (hq : q ≠ 0) (hqN : q ∣ N)
    (G H V : UpperHalfPlane → ℂ)
    (hGH : ∀ τ τ' : UpperHalfPlane, (τ' : ℂ) * ((N : ℂ) * (τ : ℂ)) = -1 →
      G τ' = (τ : ℂ) ^ k * H τ)
    (hUV : ∀ τ τ' : UpperHalfPlane, (τ' : ℂ) * ((N : ℂ) * (τ : ℂ)) = -1 →
      ModularForm.heckeU k q H τ' = (τ : ℂ) ^ k * V τ)
    (τ : UpperHalfPlane) :
    ∑ j ∈ Finset.range q,
        (G ∣[k] (ModularGroup.S * ModularGroup.T ^ ((j : ℤ) * (N / q : ℕ)) * ModularGroup.S⁻¹ :
          SL(2, ℤ))) τ
      = (q : ℂ) ^ (1 - k) * (-(N : ℂ)) ^ (-k) * V (ModularForm.heckeMatrix q 0 • τ) :=
  ALTraceIdentity.main N k hq hqN G H V hGH hUV τ

end S_UpperHalfPlane_sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_fricke_heckeU
end P2MW
export P2MW.S_UpperHalfPlane_sum_slash_S_mul_T_zpow_mul_S_inv_apply_eq_of_fricke_heckeU (solution)
