-- Prove2me | solution 2 for PhaseCut.Tight.Mmat_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:27:08.724547+00:00
-- url     : https://prove2.me/submissions/a11e8cc5-fe95-4732-8f30-eab440f65e29

import Mathlib
import Definitions.Def_PhaseCut_Tight_Defs

set_option autoImplicit false


open PhaseCut.Tight Matrix
open scoped ComplexOrder

lemma ypc_AhA_unit {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (hA : Function.Injective A.mulVec) :
    IsUnit (Aᴴ * A).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  have hz : (Aᴴ * A) *ᵥ (x - y) = 0 := by rw [Matrix.mulVec_sub]; exact sub_eq_zero.mpr hxy
  have h2 : star (A *ᵥ (x - y)) ⬝ᵥ (A *ᵥ (x - y)) = 0 := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hz]
    simp
  have h3 : A *ᵥ (x - y) = 0 := by
    exact dotProduct_star_self_eq_zero.mp h2
  have h4 : A *ᵥ (x - y) = A *ᵥ 0 := by rw [h3]; simp
  exact sub_eq_zero.mp (hA h4)

lemma ypc_pinv_mul {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (hA : Function.Injective A.mulVec) :
    pinv A * A = 1 := by
  unfold pinv
  rw [Matrix.mul_assoc]
  exact Matrix.nonsing_inv_mul _ (ypc_AhA_unit A hA)


lemma ypc_Dherm {n : ℕ} (b : Fin n → ℝ) : (D b)ᴴ = D b := by
  unfold D
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext i
  simp

theorem solution {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (b : Fin n → ℝ)
    (hA : Function.Injective A.mulVec) :
    (Mmat A b).PosSemidef := by
  have hu := ypc_AhA_unit A hA
  have hX : Aᴴ * A * (Aᴴ * A)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hXh : ((Aᴴ * A)⁻¹)ᴴ = (Aᴴ * A)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv]
    simp [Matrix.conjTranspose_mul]
  set Pr : Matrix (Fin n) (Fin n) ℂ := A * pinv A with hPr
  have hPrh : Prᴴ = Pr := by
    rw [hPr]; unfold pinv
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hXh, Matrix.mul_assoc]
  have hPr2 : Pr * Pr = Pr := by
    rw [hPr]; unfold pinv
    calc A * ((Aᴴ * A)⁻¹ * Aᴴ) * (A * ((Aᴴ * A)⁻¹ * Aᴴ))
        = A * ((Aᴴ * A)⁻¹ * (Aᴴ * A * (Aᴴ * A)⁻¹) * Aᴴ) := by simp only [Matrix.mul_assoc]
      _ = A * ((Aᴴ * A)⁻¹ * Aᴴ) := by rw [hX]; simp only [Matrix.mul_one]
  have hC : (1 - Pr)ᴴ * (1 - Pr) = 1 - Pr := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPrh]
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hPr2]
    simp
  have hpsd : (1 - Pr).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self (1 - Pr)
    rwa [hC] at this
  unfold Mmat
  have := hpsd.conjTranspose_mul_mul_same (D b)
  rwa [ypc_Dherm] at this
