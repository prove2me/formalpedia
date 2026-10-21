-- Prove2me | solution 1 for WassTwoStage.Copositive.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T10:21:49.348372+00:00
-- url     : https://prove2.me/submissions/d7f8b1f3-00e7-4d41-b850-5d0f5c18a94b

import Mathlib
import Definitions.Def_WassTwoStage_Copositive_Cones

open Matrix WassTwoStage.Copositive

-- Hanasusanto and Kuhn, arXiv:1609.07505v3, Lemma 4, p. 16.
-- Formalization by OpenAI Codex under Alexander Richard Towell's direction.
-- Uses Mathlib's proved completion-of-squares identity; no open theorem imports.
theorem solution {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n n ℝ)
    (hA : A.PosDef) (hC : C.IsSymm)
    (hS : StrictlyCopositive (C - Bᵀ * A⁻¹ * B)) :
    StrictlyCopositive (Matrix.fromBlocks A B Bᵀ C) := by
  classical
  letI := hA.isUnit.invertible
  intro v hv hv0
  let x : m → ℝ := v ∘ Sum.inl
  let y : n → ℝ := v ∘ Sum.inr
  have hvxy : Sum.elim x y = v := Sum.elim_comp_inl_inr v
  have hBT : Bᴴ = Bᵀ := by ext i j; simp
  have heq : v ⬝ᵥ ((Matrix.fromBlocks A B Bᵀ C) *ᵥ v) =
      (x + (A⁻¹ * B) *ᵥ y) ⬝ᵥ (A *ᵥ (x + (A⁻¹ * B) *ᵥ y)) +
      y ⬝ᵥ ((C - Bᵀ * A⁻¹ * B) *ᵥ y) := by
    simpa only [star_trivial, hBT, ← dotProduct_mulVec, hvxy]
      using schur_complement_eq₁₁ B C x y hA.1
  rw [heq]
  by_cases hy : y = 0
  · have hx : x ≠ 0 := by
      intro hx
      apply hv0
      rw [← hvxy, hx, hy]
      funext i
      cases i <;> rfl
    simpa [hy] using hA.dotProduct_mulVec_pos hx
  · have hn := hA.posSemidef.dotProduct_mulVec_nonneg (x + (A⁻¹ * B) *ᵥ y)
    have hp := hS y (fun j => hv (Sum.inr j)) hy
    simpa only [star_trivial] using add_pos_of_nonneg_of_pos hn hp
