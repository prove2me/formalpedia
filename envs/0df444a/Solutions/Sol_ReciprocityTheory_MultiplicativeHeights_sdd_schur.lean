-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sdd_schur
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:05:54.46493+00:00
-- url     : https://prove2.me/submissions/de2c893b-83e4-4393-923e-18537c3d9fd9

import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegSt
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiDegDA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix NumberField
open scoped ComplexOrder MatrixOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {r k₀ k₁ : ℕ} (B : Matrix (Fin r) (Fin k₀) ℂ) (C : Matrix (Fin r) (Fin k₁) ℂ)
    (H : Matrix (Fin r) (Fin r) ℂ) (hH : Hᴴ = H) (hG : (Bᴴ * H * B).IsHermitian)
    (hu : IsUnit (Bᴴ * H * B).det) :
    Cᴴ * H * C - (Cᴴ * H * B) * (Bᴴ * H * B)⁻¹ * (Bᴴ * H * C) =
      (C - B * ((Bᴴ * H * B)⁻¹ * (Bᴴ * H * C)))ᴴ * H *
        (C - B * ((Bᴴ * H * B)⁻¹ * (Bᴴ * H * C))) := by
  set G := Bᴴ * H * B with hGdef
  have hGG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul G hu
  have hGinvH : (G⁻¹)ᴴ = G⁻¹ := by rw [conjTranspose_nonsing_inv, hG.eq]
  have hYH : (Bᴴ * H * C)ᴴ = Cᴴ * H * B := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hH, Matrix.mul_assoc]
  have hXh : (G⁻¹ * (Bᴴ * H * C))ᴴ = (Cᴴ * H * B) * G⁻¹ := by
    rw [conjTranspose_mul, hYH, hGinvH]
  have hcanc : ∀ Z : Matrix (Fin k₀) (Fin k₁) ℂ, G⁻¹ * (Bᴴ * (H * (B * Z))) = Z := by
    intro Z
    have hz : Bᴴ * (H * (B * Z)) = G * Z := by simp only [hGdef, Matrix.mul_assoc]
    rw [hz, ← Matrix.mul_assoc, hGG, Matrix.one_mul]
  rw [conjTranspose_sub, conjTranspose_mul, hXh]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hcanc]
  abel
end ReciprocityTheory.MultiplicativeHeights
