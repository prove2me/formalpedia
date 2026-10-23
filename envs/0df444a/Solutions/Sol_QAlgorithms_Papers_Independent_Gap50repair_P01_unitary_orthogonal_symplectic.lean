-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap50repair.P01.unitary_orthogonal_symplectic
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T17:34:11.134919+00:00
-- url     : https://prove2.me/submissions/196060a2-5298-4eec-ba5a-67c7e047e73d

import Definitions.Def_QAlgorithms_Papers_Independent_Gap50repair_P01
noncomputable section

open scoped BigOperators Matrix Matrix.Norms.Frobenius

open QAlgorithms.Papers.Independent.Gap50repair.P01
open QAlgorithms.Papers.Independent.Dependency50.P10 (complexify)
open QAlgorithms.Papers.Independent.Frontier30.P02 (IsSymplectic canonicalJ)

namespace X4CZB

lemma comm_iff {n : ℕ} (F B C D : Matrix (Fin n) (Fin n) ℝ) :
    CommutesWithComplexStructure (Matrix.fromBlocks F B C D) ↔ D = F ∧ C = -B := by
  unfold CommutesWithComplexStructure jMatrix omegaMatrix
  rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_inj]
  simp only [Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, Matrix.zero_mul, Matrix.one_mul,
    Matrix.neg_mul, zero_add, add_zero]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h2.symm, by rw [← h1]⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨by simp, rfl, rfl, by simp⟩

lemma J_eq (n : ℕ) : canonicalJ n = jMatrix n := by
  unfold canonicalJ jMatrix omegaMatrix
  rw [Matrix.fromBlocks_neg]; simp

lemma orth_iff {n : ℕ} (F C : Matrix (Fin n) (Fin n) ℝ) :
    IsOrthogonal (Matrix.fromBlocks F (-C) C F) ↔ Fᵀ * F + Cᵀ * C = 1 ∧ Fᵀ * C = Cᵀ * F := by
  unfold IsOrthogonal
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one,
    Matrix.fromBlocks_inj]
  simp only [Matrix.transpose_neg, Matrix.mul_neg, Matrix.neg_mul, neg_neg]
  constructor
  · rintro ⟨h1, h2, -, -⟩
    refine ⟨h1, ?_⟩
    have := h2; rw [add_comm, ← sub_eq_add_neg, sub_eq_zero] at this; exact this.symm
  · rintro ⟨h1, h2⟩
    refine ⟨h1, by rw [h2]; abel, by rw [h2]; abel, by rw [add_comm]; exact h1⟩

lemma cam_mul {n : ℕ} (F C : Matrix (Fin n) (Fin n) ℝ) :
    (complexActionMatrix (Matrix.fromBlocks F (-C) C F))ᴴ *
        complexActionMatrix (Matrix.fromBlocks F (-C) C F) =
      (Fᵀ * F + Cᵀ * C).map (fun x : ℝ => (x : ℂ)) +
        Complex.I • (Fᵀ * C - Cᵀ * F).map (fun x : ℝ => (x : ℂ)) := by
  ext i j
  apply Complex.ext <;>
  simp [complexActionMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.mul_re,
    Complex.mul_im, Finset.sum_add_distrib, Finset.sum_sub_distrib] <;> ring

lemma unit_iff {n : ℕ} (F C : Matrix (Fin n) (Fin n) ℝ) :
    (complexActionMatrix (Matrix.fromBlocks F (-C) C F))ᴴ *
        complexActionMatrix (Matrix.fromBlocks F (-C) C F) = 1 ↔
      Fᵀ * F + Cᵀ * C = 1 ∧ Fᵀ * C = Cᵀ * F := by
  rw [cam_mul]
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · ext i j
      have := congrArg Complex.re (congrFun₂ h i j)
      simpa [Matrix.one_apply, apply_ite Complex.re] using this
    · rw [← sub_eq_zero]; ext i j
      have := congrArg Complex.im (congrFun₂ h i j)
      simpa [Matrix.one_apply, apply_ite Complex.im] using this
  · rintro ⟨h1, h2⟩
    rw [h1, h2, sub_self]
    ext i j
    simp [Matrix.one_apply, apply_ite]

theorem main {n : ℕ} (A : GroupedRealMatrix n) :
    IsUnitaryReal A ↔ IsOrthogonal A ∧ IsSymplectic A := by
  obtain ⟨F, B, C, D, rfl⟩ : ∃ F B C D, A = Matrix.fromBlocks F B C D :=
    ⟨_, _, _, _, (Matrix.fromBlocks_toBlocks A).symm⟩
  have key : ∀ A : GroupedRealMatrix n, IsOrthogonal A → CommutesWithComplexStructure A →
      IsSymplectic A := by
    intro A ho hc
    unfold IsSymplectic
    rw [J_eq, Matrix.mul_assoc, ← hc, ← Matrix.mul_assoc, ho, Matrix.one_mul]
  constructor
  · rintro ⟨hc, hu⟩
    have hc' := hc
    rw [comm_iff] at hc'
    obtain ⟨rfl, hC⟩ := hc'
    obtain rfl : B = -C := by rw [hC, neg_neg]
    have ho := (orth_iff _ C).2 ((unit_iff _ C).1 hu)
    exact ⟨ho, key _ ho hc⟩
  · rintro ⟨ho, hs⟩
    have hc : CommutesWithComplexStructure (Matrix.fromBlocks F B C D) := by
      unfold IsSymplectic at hs
      unfold IsOrthogonal at ho
      rw [J_eq] at hs
      have ho' : Matrix.fromBlocks F B C D * (Matrix.fromBlocks F B C D)ᵀ = 1 :=
        mul_eq_one_comm.1 ho
      unfold CommutesWithComplexStructure
      calc Matrix.fromBlocks F B C D * jMatrix n
          = Matrix.fromBlocks F B C D * ((Matrix.fromBlocks F B C D)ᵀ * jMatrix n *
              Matrix.fromBlocks F B C D) := by rw [hs]
        _ = (Matrix.fromBlocks F B C D * (Matrix.fromBlocks F B C D)ᵀ) * jMatrix n *
              Matrix.fromBlocks F B C D := by simp only [Matrix.mul_assoc]
        _ = jMatrix n * Matrix.fromBlocks F B C D := by rw [ho', Matrix.one_mul]
    refine ⟨hc, ?_⟩
    have hc' := hc
    rw [comm_iff] at hc'
    obtain ⟨rfl, hC⟩ := hc'
    obtain rfl : B = -C := by rw [hC, neg_neg]
    exact (unit_iff _ C).2 ((orth_iff _ C).1 ho)

end X4CZB

theorem solution {n : ℕ} (A : GroupedRealMatrix n) :
    IsUnitaryReal A ↔ IsOrthogonal A ∧ IsSymplectic A := X4CZB.main A
