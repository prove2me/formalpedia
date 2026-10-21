-- Prove2me | solution 2 for WassTwoStage.Copositive.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:34:40.553032+00:00
-- url     : https://prove2.me/submissions/baa5aa88-ed09-4ad7-8992-179d54fd5335

import Mathlib
import Definitions.Def_WassTwoStage_Copositive_Cones

set_option autoImplicit false
open Matrix WassTwoStage.Copositive

theorem solution {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
    (A : Matrix m m ℝ) (B : Matrix m n ℝ) (C : Matrix n n ℝ)
    (hA : A.PosDef) (hC : C.IsSymm)
    (hS : StrictlyCopositive (C - Bᵀ * A⁻¹ * B)) :
    StrictlyCopositive (Matrix.fromBlocks A B Bᵀ C) := by
  intro v hv hv0
  set u : m → ℝ := fun i => v (Sum.inl i) with hu
  set w : n → ℝ := fun j => v (Sum.inr j) with hw
  have hvuw : v = Sum.elim u w := by
    ext i; rcases i with i | i <;> simp [hu, hw]
  have hw0 : 0 ≤ w := fun i => hv _
  have hAs : Aᵀ = A := hA.isHermitian.eq
  have hAdet : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).1 hA.isUnit
  have hAinvA : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A hAdet
  set r : m → ℝ := A⁻¹ *ᵥ (B *ᵥ w) with hr
  have f1 : A *ᵥ r = B *ᵥ w := by
    rw [hr, Matrix.mulVec_mulVec, hAinvA, Matrix.one_mulVec]
  have f2 : r ⬝ᵥ (A *ᵥ u) = (B *ᵥ w) ⬝ᵥ u := by
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, hAs, f1]
  have f3 : w ⬝ᵥ ((Bᵀ * A⁻¹ * B) *ᵥ w) = (B *ᵥ w) ⬝ᵥ r := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec, ← Matrix.mulVec_transpose]
    rw [Matrix.transpose_transpose]
  have f4 : w ⬝ᵥ (Bᵀ *ᵥ u) = (B *ᵥ w) ⬝ᵥ u := by
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose]
    rw [Matrix.transpose_transpose]
  have hq : v ⬝ᵥ (Matrix.fromBlocks A B Bᵀ C *ᵥ v)
      = (u + r) ⬝ᵥ (A *ᵥ (u + r)) + w ⬝ᵥ ((C - Bᵀ * A⁻¹ * B) *ᵥ w) := by
    rw [hvuw, Matrix.fromBlocks_mulVec, sumElim_dotProduct_sumElim]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.mulVec_add, add_dotProduct, dotProduct_add, f1, f2, f4, Matrix.sub_mulVec,
      dotProduct_sub, f3]
    linarith [dotProduct_comm u (B *ᵥ w), dotProduct_comm r (B *ᵥ w)]
  rw [hvuw] at hv0
  rw [hvuw] at hq ⊢
  rw [hq]
  have hpsd : 0 ≤ (u + r) ⬝ᵥ (A *ᵥ (u + r)) := by
    by_cases hx : u + r = 0
    · rw [hx]; simp
    · have := hA.dotProduct_mulVec_pos hx
      simpa using this.le
  by_cases hw' : w = 0
  · have hu' : u ≠ 0 := by
      intro hu0; apply hv0; rw [hu0, hw']; ext i; rcases i with i | i <;> simp
    have hr0 : r = 0 := by simp [hr, hw']
    rw [hr0, hw']
    have := hA.dotProduct_mulVec_pos hu'
    simpa using this
  · have := hS w hw0 hw'
    linarith
