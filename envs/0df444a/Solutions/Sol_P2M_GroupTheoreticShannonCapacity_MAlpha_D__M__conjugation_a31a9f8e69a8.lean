-- Prove2me | solution 1 for P2M_GroupTheoreticShannonCapacity_MAlpha_D__M__conjugation_a31a9f8e69a8
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:47:07.467782+00:00
-- url     : https://prove2.me/submissions/46b6c611-ca77-4be2-b802-b04214dc1eec

import Mathlib.Algebra.Group.Pi.Units
import Definitions.Def_GroupTheoreticShannonCapacity_P0Matrix
import Definitions.Def_GroupTheoreticShannonCapacity_MAlpha
import Theorems.Thm_P2M_GroupTheoreticShannonCapacity_MAlpha_R__sub_one_isUnit_29a9b3d1283b
import Theorems.Thm_P2M_GroupTheoreticShannonCapacity_MAlpha_M__factorization_ff46d0e46406
import Theorems.Thm_P2M_GroupTheoreticShannonCapacity_MAlpha_D__inv_5f24521fe641
import Theorems.Thm_P2M_GroupTheoreticShannonCapacity_MAlpha_D__R__conjugation_ad4d6061ab21

set_option autoImplicit true
open GroupTheoreticShannonCapacity GroupTheoreticShannonCapacity.MAlpha
open Matrix
namespace GroupTheoreticShannonCapacity.MAlpha
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) (α β : ℝ) (hα : α ≠ -1) (hβ : β ≠ 0) :
    Dα n β * Mα n α * (Dα n β)⁻¹ =
    (β • Rα n (α * β⁻¹^n) + α • 1) * (β • Rα n (α * β⁻¹^n) - 1)⁻¹ := by
  -- Use the factorization M_α = (R_α + αI)(R_α - I)⁻¹
  set γ := α * β⁻¹^n with hγ
  have hfact := Mα_factorization n α hα
  rw [hfact]
  have hD_inv := Dα_inv n β hβ
  rw [hD_inv]
  -- Prove D_β D_β⁻¹ = I and D_β⁻¹ D_β = I
  have hDinv_D : Dα n β⁻¹ * Dα n β = 1 := by
    simp only [Dα, Matrix.diagonal_mul_diagonal]
    convert Matrix.diagonal_one using 2
    ext i; simp only [inv_pow]; field_simp
  have hD_Dinv : Dα n β * Dα n β⁻¹ = 1 := by
    simp only [Dα, Matrix.diagonal_mul_diagonal]
    convert Matrix.diagonal_one using 2
    ext i; simp only [inv_pow]; field_simp
  -- Use the conjugation formula for R_α
  have hconj := Dα_Rα_conjugation n α β hβ
  rw [hD_inv] at hconj
  -- Key lemma: D * A * D⁻¹ + α * I when A = R + α * I
  have h1 : Dα n β * (Rα n α + α • 1) * Dα n β⁻¹ = β • Rα n γ + α • 1 := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hD_Dinv]
    simp only [hconj, ← hγ]
  -- Key lemma: D * (R - I) * D⁻¹ = β * R_γ - I
  have h3 : Dα n β * (Rα n α - 1) * Dα n β⁻¹ = β • Rα n γ - 1 := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hD_Dinv, hconj, ← hγ]
  -- Key lemma: conjugation preserves inverses
  have hRsub_unit := Rα_sub_one_isUnit n hn α hα
  have hRsub_det_unit := (Matrix.isUnit_iff_isUnit_det _).mp hRsub_unit
  have h2 : Dα n β * (Rα n α - 1)⁻¹ * Dα n β⁻¹ = (β • Rα n γ - 1)⁻¹ := by
    have hinv : (β • Rα n γ - 1) * (Dα n β * (Rα n α - 1)⁻¹ * Dα n β⁻¹) = 1 := by
      rw [← h3]
      -- (D * (R - 1) * D⁻¹) * (D * (R - 1)⁻¹ * D⁻¹) = 1
      calc Dα n β * (Rα n α - 1) * Dα n β⁻¹ * (Dα n β * (Rα n α - 1)⁻¹ * Dα n β⁻¹)
          = Dα n β * (Rα n α - 1) * (Dα n β⁻¹ * Dα n β) * (Rα n α - 1)⁻¹ * Dα n β⁻¹ := by
            simp only [Matrix.mul_assoc]
        _ = Dα n β * (Rα n α - 1) * (Rα n α - 1)⁻¹ * Dα n β⁻¹ := by
            rw [hDinv_D, Matrix.mul_one]
        _ = Dα n β * 1 * Dα n β⁻¹ := by
            rw [Matrix.mul_assoc (Dα n β) (Rα n α - 1) ((Rα n α - 1)⁻¹),
                Matrix.mul_nonsing_inv _ hRsub_det_unit]
        _ = 1 := by rw [Matrix.mul_one, hD_Dinv]
    exact (Matrix.inv_eq_right_inv hinv).symm
  -- Final calculation: D * (A * B⁻¹) * D⁻¹ = (D A D⁻¹) * (D B⁻¹ D⁻¹)
  have hfinal : Dα n β * ((Rα n α + α • 1) * (Rα n α - 1)⁻¹) * Dα n β⁻¹ =
      Dα n β * (Rα n α + α • 1) * Dα n β⁻¹ * (Dα n β * (Rα n α - 1)⁻¹ * Dα n β⁻¹) := by
    simp only [Matrix.mul_assoc]
    congr 2
    rw [← Matrix.mul_assoc (Dα n β⁻¹) (Dα n β) _, hDinv_D, Matrix.one_mul]
  rw [hfinal, h1, h2]
end GroupTheoreticShannonCapacity.MAlpha
