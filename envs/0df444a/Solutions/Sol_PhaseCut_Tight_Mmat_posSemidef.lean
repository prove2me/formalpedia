-- Prove2me | solution 1 for PhaseCut.Tight.Mmat_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:16:58.445207+00:00
-- url     : https://prove2.me/submissions/4d585d76-2400-4a80-8334-1ed97c14636b

import Mathlib
import Definitions.Def_PhaseCut_Tight_Defs
set_option autoImplicit false
open Matrix PhaseCut.Tight
open scoped ComplexOrder

theorem pinv_mul_self_BB {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ)
    (hA : Function.Injective A.mulVec) : pinv A * A = 1 := by
  have h1 : (Aᴴ * A).PosDef := Matrix.PosDef.conjTranspose_mul_self A hA
  have h2 : IsUnit (Aᴴ * A).det := (Matrix.isUnit_iff_isUnit_det _).1 h1.isUnit
  unfold pinv
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h2]

theorem solution {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (b : Fin n → ℝ)
    (hA : Function.Injective A.mulVec) :
    (Mmat A b).PosSemidef := by
  have hP := pinv_mul_self_BB A hA
  set P : Matrix (Fin n) (Fin n) ℂ := 1 - A * pinv A with hPdef
  have hH : (A * pinv A)ᴴ = A * pinv A := by
    unfold pinv
    simp [Matrix.conjTranspose_mul, Matrix.conjTranspose_nonsing_inv, Matrix.mul_assoc]
  have hPh : Pᴴ = P := by
    rw [hPdef, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hH]
  have hPP : P * P = P := by
    rw [hPdef]
    have : (A * pinv A) * (A * pinv A) = A * pinv A := by
      calc (A * pinv A) * (A * pinv A) = A * (pinv A * A) * pinv A := by simp only [Matrix.mul_assoc]
        _ = A * pinv A := by rw [hP]; simp
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, this, Matrix.one_mul]
    abel
  have hDh : (D b)ᴴ = D b := by
    unfold D
    rw [Matrix.diagonal_conjTranspose]
    congr 1
    funext i
    simp
  have : Mmat A b = (P * D b)ᴴ * (P * D b) := by
    rw [Matrix.conjTranspose_mul, hPh, hDh]
    unfold Mmat
    rw [← hPdef]
    calc D b * P * D b = D b * (P * P) * D b := by rw [hPP]
      _ = D b * P * (P * D b) := by simp only [Matrix.mul_assoc]
  rw [this]
  exact Matrix.posSemidef_conjTranspose_mul_self _
