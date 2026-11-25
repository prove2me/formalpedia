-- Prove2me | solution 1 for Planks.rot_orthonormal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:38:25.843592+00:00
-- url     : https://prove2.me/submissions/87e799a8-544e-4f8a-8896-d6065bcf0a7b

module
public import Mathlib
public import Definitions.Def_BallPlank_Planks

set_option autoImplicit true
@[expose] public section
public section
open scoped RealInnerProductSpace
open Classical
noncomputable section
open Planks
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι]
omit [FiniteDimensional ℝ E] [Fintype ι]
namespace Planks
theorem _root_.solution (y : ι → E) (hy : Orthonormal ℝ y) (i j : ι) (hij : i ≠ j) (t : ℝ) :
    Orthonormal ℝ (rot y i j t) := by
  rw [orthonormal_iff_ite] at hy ⊢
  have hc := Real.cos_sq_add_sin_sq t
  have hji : j ≠ i := Ne.symm hij
  intro a b
  by_cases hai : a = i
  · subst hai
    by_cases hbi : b = a
    · subst hbi
      simp only [rot, ↓reduceIte, inner_add_left, inner_add_right, real_inner_smul_left,
        real_inner_smul_right, hy, hij, hji]
      linarith
    · by_cases hbj : b = j
      · subst hbj
        simp only [rot, ↓reduceIte, inner_add_left, inner_add_right, real_inner_smul_left,
          real_inner_smul_right, hy, hij, hji]
        ring
      · simp only [rot, ↓reduceIte, inner_add_left, real_inner_smul_left, hy, hbi, hbj,
          Ne.symm hbi, Ne.symm hbj]
        ring
  · by_cases haj : a = j
    · subst haj
      by_cases hbi : b = i
      · subst hbi
        simp only [rot, ↓reduceIte, inner_add_left, inner_add_right, real_inner_smul_left,
          real_inner_smul_right, hy, hij, hji]
        ring
      · by_cases hbj : b = a
        · subst hbj
          simp only [rot, ↓reduceIte, inner_add_left, inner_add_right, real_inner_smul_left,
            real_inner_smul_right, hy, hij, hji]
          linarith
        · simp only [rot, ↓reduceIte, inner_add_left, real_inner_smul_left, hy, hji, hbi, hbj,
            Ne.symm hbi, Ne.symm hbj]
          ring
    · by_cases hbi : b = i
      · subst hbi
        simp only [rot, ↓reduceIte, inner_add_right, real_inner_smul_right, hy, hai, haj]
        ring
      · by_cases hbj : b = j
        · subst hbj
          simp only [rot, ↓reduceIte, inner_add_right, real_inner_smul_right, hy, hji, hai, haj]
          ring
        · simp [rot, hy, hai, haj, hbi, hbj]
end Planks
