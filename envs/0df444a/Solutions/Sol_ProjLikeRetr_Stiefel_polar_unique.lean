-- Prove2me | solution 1 for ProjLikeRetr.Stiefel.polar_unique
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T10:05:17.052839+00:00
-- url     : https://prove2.me/submissions/d4431fbd-bc7f-4fc2-9ecd-bafa0a1fed1b

import Mathlib
import Definitions.Def_ProjLikeRetr_Stiefel_stiefel

open scoped Matrix

open scoped MatrixOrder in
theorem polar_unique_aux_sq {m : ℕ} (P₁ P₂ : Matrix (Fin m) (Fin m) ℝ)
    (hP₁ : P₁.PosSemidef) (hP₂ : P₂.PosSemidef) (h : P₁ * P₁ = P₂ * P₂) : P₁ = P₂ := by
  have := (CFC.sq_eq_sq_iff P₁ P₂ hP₁.nonneg hP₂.nonneg).mp (by simpa [sq] using h)
  exact this

theorem polar_unique_aux_gram {n m : ℕ} (W : Matrix (Fin n) (Fin m) ℝ)
    (P : Matrix (Fin m) (Fin m) ℝ) (hW : W ∈ ProjLikeRetr.Stiefel.stiefel n m)
    (hP : P.PosSemidef) : (W * P)ᵀ * (W * P) = P * P := by
  have hW' : Wᵀ * W = 1 := hW
  have hPt : Pᵀ = P := by
    have := hP.1
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] at this
    exact this
  rw [Matrix.transpose_mul, hPt, Matrix.mul_assoc, ← Matrix.mul_assoc Wᵀ, hW', Matrix.one_mul]

namespace ProjLikeRetr.Stiefel

theorem polar_unique_surj {n m : ℕ} (X : Matrix (Fin n) (Fin m) ℝ) (hrank : X.rank = m)
    (W : Matrix (Fin n) (Fin m) ℝ) (P : Matrix (Fin m) (Fin m) ℝ) (h : X = W * P) :
    Function.Surjective P.mulVecLin := by
  have h1 : P.rank = m := by
    apply le_antisymm (Matrix.rank_le_width P)
    calc m = X.rank := hrank.symm
      _ = (W * P).rank := by rw [h]
      _ ≤ P.rank := Matrix.rank_mul_le_right W P
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_top_of_finrank_eq
  rw [Module.finrank_fin_fun]
  exact h1

end ProjLikeRetr.Stiefel

open ProjLikeRetr.Stiefel in
theorem solution {n m : ℕ} (X : Matrix (Fin n) (Fin m) ℝ) (hrank : X.rank = m)
    (W₁ W₂ : Matrix (Fin n) (Fin m) ℝ) (P₁ P₂ : Matrix (Fin m) (Fin m) ℝ)
    (hW₁ : W₁ ∈ stiefel n m) (hW₂ : W₂ ∈ stiefel n m)
    (hP₁ : P₁.PosSemidef) (hP₂ : P₂.PosSemidef) (h₁ : X = W₁ * P₁) (h₂ : X = W₂ * P₂) :
    W₁ = W₂ ∧ P₁ = P₂ := by
  have hP : P₁ = P₂ := by
    apply polar_unique_aux_sq P₁ P₂ hP₁ hP₂
    rw [← polar_unique_aux_gram W₁ P₁ hW₁ hP₁, ← polar_unique_aux_gram W₂ P₂ hW₂ hP₂, ← h₁, ← h₂]
  refine ⟨?_, hP⟩
  subst hP
  have hs := polar_unique_surj X hrank W₁ P₁ h₁
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro u
  obtain ⟨v, rfl⟩ := hs u
  simp only [Matrix.toLin'_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
  rw [← h₁, h₂]
