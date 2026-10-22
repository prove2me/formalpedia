-- Prove2me | solution 1 for RobinsonSR.Schur.inclusion_iff_schur
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T00:21:38.48846+00:00
-- url     : https://prove2.me/submissions/e5a5026b-9ee3-4f6a-bf15-6e5e1f217349

import Mathlib
import Definitions.Def_RobinsonSR_Schur_Setting



namespace RobinsonSR.Schur

open scoped RealInnerProductSpace Matrix
open WithLp

lemma g_tel {m n : Type*} [Fintype n] [DecidableEq n] (M : Matrix m n ℝ) (v : EuclideanSpace ℝ n) :
    M.toEuclideanLin v = toLp 2 (M *ᵥ ofLp v) := rfl

def g_join {r s : ℕ} (a : EuclideanSpace ℝ (Fin r)) (b : EuclideanSpace ℝ (Fin s)) :
    EuclideanSpace ℝ (Fin r ⊕ Fin s) := toLp 2 (Sum.elim (ofLp a) (ofLp b))

lemma g_upper_join {r s : ℕ} (a : EuclideanSpace ℝ (Fin r)) (b : EuclideanSpace ℝ (Fin s)) :
    upperBlock (g_join a b) = a := rfl
lemma g_lower_join {r s : ℕ} (a : EuclideanSpace ℝ (Fin r)) (b : EuclideanSpace ℝ (Fin s)) :
    lowerBlock (g_join a b) = b := rfl

lemma g_upper_sub {r s : ℕ} (a b : EuclideanSpace ℝ (Fin r ⊕ Fin s)) :
    upperBlock (a - b) = upperBlock a - upperBlock b := rfl
lemma g_lower_sub {r s : ℕ} (a b : EuclideanSpace ℝ (Fin r ⊕ Fin s)) :
    lowerBlock (a - b) = lowerBlock a - lowerBlock b := rfl

lemma g_inner_split {r s : ℕ} (u v : EuclideanSpace ℝ (Fin r ⊕ Fin s)) :
    ⟪u, v⟫ = ⟪upperBlock u, upperBlock v⟫ + ⟪lowerBlock u, lowerBlock v⟫ := by
  simp [PiLp.inner_apply, Fintype.sum_sum_type, upperBlock, lowerBlock]

lemma g_nc_prod {r s : ℕ} (K : Set (EuclideanSpace ℝ (Fin s))) (v w : EuclideanSpace ℝ (Fin r ⊕ Fin s)) :
    v ∈ normalCone (prodSet K) w ↔ upperBlock v = 0 ∧ lowerBlock v ∈ normalCone K (lowerBlock w) := by
  constructor
  · rintro ⟨hw, h⟩
    have h1 := h (g_join (upperBlock w + upperBlock v) (lowerBlock w)) (by
      show lowerBlock (g_join _ _) ∈ K
      rw [g_lower_join]; exact hw)
    rw [g_inner_split, g_upper_sub, g_lower_sub, g_upper_join, g_lower_join] at h1
    simp only [add_sub_cancel_left, sub_self, inner_zero_right, add_zero] at h1
    refine ⟨?_, hw, fun c hc => ?_⟩
    · have : ‖upperBlock v‖ ^ 2 ≤ 0 := by rw [← real_inner_self_eq_norm_sq]; exact h1
      have : ‖upperBlock v‖ = 0 := by nlinarith [norm_nonneg (upperBlock v)]
      exact norm_eq_zero.mp this
    · have h2 := h (g_join (upperBlock w) c) (by
        show lowerBlock (g_join _ _) ∈ K
        rw [g_lower_join]; exact hc)
      rw [g_inner_split, g_upper_sub, g_lower_sub, g_upper_join, g_lower_join] at h2
      simpa using h2
  · rintro ⟨h0, hw, h⟩
    refine ⟨hw, fun c hc => ?_⟩
    rw [g_inner_split, h0, g_lower_sub]
    simpa using h _ hc

lemma g_upper_A {r s : ℕ} (A₁₁ : Matrix (Fin r) (Fin r) ℝ) (A₁₂ : Matrix (Fin r) (Fin s) ℝ)
    (A₂₁ : Matrix (Fin s) (Fin r) ℝ) (A₂₂ : Matrix (Fin s) (Fin s) ℝ) (w : EuclideanSpace ℝ (Fin r ⊕ Fin s)) :
    upperBlock ((Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).toEuclideanLin w) =
      A₁₁.toEuclideanLin (upperBlock w) + A₁₂.toEuclideanLin (lowerBlock w) := by
  ext i
  simp [g_tel, upperBlock, lowerBlock, Matrix.fromBlocks_mulVec]
  rfl

lemma g_lower_A {r s : ℕ} (A₁₁ : Matrix (Fin r) (Fin r) ℝ) (A₁₂ : Matrix (Fin r) (Fin s) ℝ)
    (A₂₁ : Matrix (Fin s) (Fin r) ℝ) (A₂₂ : Matrix (Fin s) (Fin s) ℝ) (w : EuclideanSpace ℝ (Fin r ⊕ Fin s)) :
    lowerBlock ((Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).toEuclideanLin w) =
      A₂₁.toEuclideanLin (upperBlock w) + A₂₂.toEuclideanLin (lowerBlock w) := by
  ext i
  simp [g_tel, upperBlock, lowerBlock, Matrix.fromBlocks_mulVec]
  rfl


lemma g_inv_iff {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.det ≠ 0) (x b : EuclideanSpace ℝ (Fin n)) :
    A.toEuclideanLin x = b ↔ x = (A⁻¹).toEuclideanLin b := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  constructor
  · rintro rfl
    simp only [g_tel, ofLp_toLp, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  · rintro rfl
    simp only [g_tel, ofLp_toLp, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]

lemma g_schur_lin {r s : ℕ} (A₁₁ : Matrix (Fin r) (Fin r) ℝ) (A₁₂ : Matrix (Fin r) (Fin s) ℝ)
    (A₂₁ : Matrix (Fin s) (Fin r) ℝ) (A₂₂ : Matrix (Fin s) (Fin s) ℝ) (x : EuclideanSpace ℝ (Fin s)) :
    (schur A₁₁ A₁₂ A₂₁ A₂₂).toEuclideanLin x =
      A₂₂.toEuclideanLin x - A₂₁.toEuclideanLin ((A₁₁⁻¹).toEuclideanLin (A₁₂.toEuclideanLin x)) := by
  simp only [g_tel, ofLp_toLp, schur, Matrix.sub_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rfl

theorem inclusion_core (r s : ℕ)
    (A₁₁ : Matrix (Fin r) (Fin r) ℝ)
    (A₁₂ : Matrix (Fin r) (Fin s) ℝ)
    (A₂₁ : Matrix (Fin s) (Fin r) ℝ)
    (A₂₂ : Matrix (Fin s) (Fin s) ℝ)
    (hA₁₁ : A₁₁.det ≠ 0) (K : Set (EuclideanSpace ℝ (Fin s)))
    (y w : EuclideanSpace ℝ (Fin r ⊕ Fin s)) :
    (y - (Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).toEuclideanLin w ∈
      normalCone (prodSet K) w) ↔
    (upperBlock w = (A₁₁⁻¹).toEuclideanLin (upperBlock y) -
      (A₁₁⁻¹).toEuclideanLin (A₁₂.toEuclideanLin (lowerBlock w))) ∧
    (lowerBlock y - A₂₁.toEuclideanLin ((A₁₁⁻¹).toEuclideanLin (upperBlock y)) -
      (schur A₁₁ A₁₂ A₂₁ A₂₂).toEuclideanLin (lowerBlock w) ∈
      normalCone K (lowerBlock w)) := by
  rw [g_nc_prod, g_upper_sub, g_lower_sub, g_upper_A, g_lower_A]
  have key : upperBlock y - (A₁₁.toEuclideanLin (upperBlock w) + A₁₂.toEuclideanLin (lowerBlock w)) = 0 ↔
      upperBlock w = (A₁₁⁻¹).toEuclideanLin (upperBlock y) -
        (A₁₁⁻¹).toEuclideanLin (A₁₂.toEuclideanLin (lowerBlock w)) := by
    rw [sub_eq_zero, eq_comm, ← eq_sub_iff_add_eq, g_inv_iff _ hA₁₁, map_sub]
  rw [key]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    convert h2 using 1
    rw [h1, map_sub, g_schur_lin]; abel
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    convert h2 using 1
    rw [h1, map_sub, g_schur_lin]; abel

end RobinsonSR.Schur

open RobinsonSR.Schur


theorem solution (r s : ℕ) (hr : 0 < r) (hs : 0 < s)
    (A₁₁ : Matrix (Fin r) (Fin r) ℝ)
    (A₁₂ : Matrix (Fin r) (Fin s) ℝ)
    (A₂₁ : Matrix (Fin s) (Fin r) ℝ)
    (A₂₂ : Matrix (Fin s) (Fin s) ℝ)
    (hA₁₁ : A₁₁.det ≠ 0) (K : Set (EuclideanSpace ℝ (Fin s)))
    (y w : EuclideanSpace ℝ (Fin r ⊕ Fin s)) :
    (y - (Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).toEuclideanLin w ∈
      normalCone (prodSet K) w) ↔
    (upperBlock w = (A₁₁⁻¹).toEuclideanLin (upperBlock y) -
      (A₁₁⁻¹).toEuclideanLin (A₁₂.toEuclideanLin (lowerBlock w))) ∧
    (lowerBlock y - A₂₁.toEuclideanLin ((A₁₁⁻¹).toEuclideanLin (upperBlock y)) -
      (schur A₁₁ A₁₂ A₂₁ A₂₂).toEuclideanLin (lowerBlock w) ∈
      normalCone K (lowerBlock w)) := by
  exact inclusion_core r s A₁₁ A₁₂ A₂₁ A₂₂ hA₁₁ K y w
