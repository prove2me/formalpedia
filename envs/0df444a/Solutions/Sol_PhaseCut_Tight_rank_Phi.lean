-- Prove2me | solution 1 for PhaseCut.Tight.rank_Phi
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:14:56.788237+00:00
-- url     : https://prove2.me/submissions/2f692170-50fb-48ce-b23b-3a056da44f7d

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

theorem rank_left_BB {a b c : Type} [Fintype a] [Fintype b] [Fintype c] [DecidableEq a] [DecidableEq b] [DecidableEq c]
    (A : Matrix a b ℂ) (P : Matrix b a ℂ) (h : P * A = 1) (Y : Matrix b c ℂ) :
    (A * Y).rank = Y.rank := by
  apply le_antisymm (Matrix.rank_mul_le_right _ _)
  calc Y.rank = (P * (A * Y)).rank := by rw [← Matrix.mul_assoc, h, Matrix.one_mul]
    _ ≤ (A * Y).rank := Matrix.rank_mul_le_right _ _

theorem rank_right_BB {a b c : Type} [Fintype a] [Fintype b] [Fintype c] [DecidableEq a] [DecidableEq b] [DecidableEq c]
    (B : Matrix b c ℂ) (Q : Matrix c b ℂ) (h : B * Q = 1) (Y : Matrix a b ℂ) :
    (Y * B).rank = Y.rank := by
  apply le_antisymm (Matrix.rank_mul_le_left _ _)
  calc Y.rank = (Y * B * Q).rank := by rw [Matrix.mul_assoc, h, Matrix.mul_one]
    _ ≤ (Y * B).rank := Matrix.rank_mul_le_left _ _

theorem solution {n p : ℕ} (A : Matrix (Fin n) (Fin p) ℂ) (b : Fin n → ℝ)
    (hA : Function.Injective A.mulVec) (hb : ∀ i, b i ≠ 0) :
    ∀ X : Matrix (Fin p) (Fin p) ℂ, X.rank = (Phi A b X).rank := by
  intro X
  have hP := pinv_mul_self_BB A hA
  have hD := D_mul_Dinv_BB b hb
  have hDi := Dinv_mul_D_BB b hb
  unfold Phi
  rw [rank_right_BB (Dinv b) (D b) hDi, rank_right_BB Aᴴ (pinv A)ᴴ (by rw [← Matrix.conjTranspose_mul, hP]; simp),
    rank_left_BB (Dinv b * A) (pinv A * D b) (by
      calc pinv A * D b * (Dinv b * A) = pinv A * (D b * Dinv b) * A := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hD, Matrix.mul_one, hP])]
