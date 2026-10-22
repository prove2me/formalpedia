-- Prove2me | solution 1 for PhaseCut.Tight.trace_eq_trace_B_Phi
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:14:51.124664+00:00
-- url     : https://prove2.me/submissions/376317ee-afe3-495b-9ebf-85df3c159a14

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

theorem D_mul_Dinv_BB {n : ℕ} (b : Fin n → ℝ) (hb : ∀ i, b i ≠ 0) : D b * Dinv b = 1 := by
  unfold D Dinv
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  have : (b i : ℂ) ≠ 0 := by exact_mod_cast hb i
  simp [this]

theorem Dinv_mul_D_BB {n : ℕ} (b : Fin n → ℝ) (hb : ∀ i, b i ≠ 0) : Dinv b * D b = 1 := by
  unfold D Dinv
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  have : (b i : ℂ) ≠ 0 := by exact_mod_cast hb i
  simp [this]

theorem solution {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (b : Fin n → ℝ)
    (hA : Function.Injective A.mulVec) (hb : ∀ i, b i ≠ 0) :
    ∀ X : Matrix (Fin p) (Fin p) ℂ, X.trace = (Bmat A b * Phi A b X).trace := by
  intro X
  have hP := pinv_mul_self_BB A hA
  have hD := D_mul_Dinv_BB b hb
  have hDi := Dinv_mul_D_BB b hb
  have e1 : Bmat A b * Phi A b X = D b * ((pinv A)ᴴ * X * Aᴴ) * Dinv b := by
    unfold Bmat Phi
    calc D b * (pinv A)ᴴ * pinv A * D b * (Dinv b * A * X * Aᴴ * Dinv b)
        = D b * (pinv A)ᴴ * pinv A * (D b * Dinv b) * A * X * Aᴴ * Dinv b := by
          simp only [Matrix.mul_assoc]
      _ = D b * ((pinv A)ᴴ * (pinv A * A) * X * Aᴴ) * Dinv b := by
          rw [hD]; simp only [Matrix.mul_assoc, Matrix.mul_one]
      _ = D b * ((pinv A)ᴴ * X * Aᴴ) * Dinv b := by rw [hP]; simp
  rw [e1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hDi, Matrix.one_mul,
    Matrix.trace_mul_comm ((pinv A)ᴴ * X) Aᴴ, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hP]
  simp
