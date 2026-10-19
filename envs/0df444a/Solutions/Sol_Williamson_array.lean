-- Prove2me | solution 1 for Williamson_array
-- status  : ACCEPTED   (prove)
-- author  : @ronr
-- created : 2026-09-06T00:55:45.218851+00:00
-- url     : https://prove2.me/submissions/92d7a365-8cb7-4a0a-9af8-78b37e9b7baa

import Mathlib

open Matrix

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Entries of a block matrix are `±1` when all four blocks have `±1` entries. -/
private lemma fromBlocks_pm (X Y Z Wm : Matrix ι ι ℝ)
    (hX : ∀ i j, X i j = 1 ∨ X i j = -1) (hY : ∀ i j, Y i j = 1 ∨ Y i j = -1)
    (hZ : ∀ i j, Z i j = 1 ∨ Z i j = -1) (hW : ∀ i j, Wm i j = 1 ∨ Wm i j = -1) :
    ∀ i j, (Matrix.fromBlocks X Y Z Wm) i j = 1 ∨ (Matrix.fromBlocks X Y Z Wm) i j = -1 := by
  intro i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂]
  · exact hX i j
  · exact hY i j
  · exact hZ i j
  · exact hW i j

private lemma neg_pm (X : Matrix ι ι ℝ) (hX : ∀ i j, X i j = 1 ∨ X i j = -1) :
    ∀ i j, (-X) i j = 1 ∨ (-X) i j = -1 := by
  intro i j
  rcases hX i j with h | h <;> simp [Matrix.neg_apply, h]

private lemma transpose_pm (X : Matrix ι ι ℝ) (hX : ∀ i j, X i j = 1 ∨ X i j = -1) :
    ∀ i j, Xᵀ i j = 1 ∨ Xᵀ i j = -1 := fun i j => hX j i

private lemma fromBlocks_smul_one (c : ℝ) :
    Matrix.fromBlocks (c • (1 : Matrix ι ι ℝ)) 0 0 (c • (1 : Matrix ι ι ℝ)) =
      c • (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) := by
  rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul, smul_zero]

/-- **W1a.** For commuting symmetric `X, Y`, the "complex-type" block matrix
`[[X, Y], [-Y, X]]` satisfies `M Mᵀ = [[X²+Y², 0], [0, X²+Y²]]`. -/
private lemma block_complex_mul_transpose (X Y : Matrix ι ι ℝ)
    (hXs : Xᵀ = X) (hYs : Yᵀ = Y) (hcomm : X * Y = Y * X) :
    (Matrix.fromBlocks X Y (-Y) X) * (Matrix.fromBlocks X Y (-Y) X)ᵀ =
      Matrix.fromBlocks (X * X + Y * Y) 0 0 (X * X + Y * Y) := by
  have ht : (Matrix.fromBlocks X Y (-Y) X)ᵀ = Matrix.fromBlocks X (-Y) Y X := by
    rw [Matrix.fromBlocks_transpose, Matrix.transpose_neg, hXs, hYs]
  rw [ht, Matrix.fromBlocks_multiply]
  have e12 : X * (-Y) + Y * X = 0 := by rw [Matrix.mul_neg, hcomm]; abel
  have e21 : (-Y) * X + X * Y = 0 := by rw [Matrix.neg_mul, hcomm]; abel
  have e22 : (-Y) * (-Y) + X * X = X * X + Y * Y := by rw [neg_mul_neg]; abel
  rw [e12, e21, e22]

/-- **W1b.** The same product in the other order. -/
private lemma block_complex_transpose_mul (X Y : Matrix ι ι ℝ)
    (hXs : Xᵀ = X) (hYs : Yᵀ = Y) (hcomm : X * Y = Y * X) :
    (Matrix.fromBlocks X Y (-Y) X)ᵀ * (Matrix.fromBlocks X Y (-Y) X) =
      Matrix.fromBlocks (X * X + Y * Y) 0 0 (X * X + Y * Y) := by
  have ht : (Matrix.fromBlocks X Y (-Y) X)ᵀ = Matrix.fromBlocks X (-Y) Y X := by
    rw [Matrix.fromBlocks_transpose, Matrix.transpose_neg, hXs, hYs]
  rw [ht, Matrix.fromBlocks_multiply]
  have e11 : X * X + (-Y) * (-Y) = X * X + Y * Y := by rw [neg_mul_neg]
  have e12 : X * Y + (-Y) * X = 0 := by rw [Matrix.neg_mul, hcomm]; abel
  have e21 : Y * X + X * (-Y) = 0 := by rw [Matrix.mul_neg, hcomm]; abel
  have e22 : Y * Y + X * X = X * X + Y * Y := by abel
  rw [e11, e12, e21, e22]

/-- **W1c.** Two "complex-type" blocks built from pairwise commuting matrices commute. -/
private lemma block_complex_comm (A B C D : Matrix ι ι ℝ)
    (hAC : A * C = C * A) (hAD : A * D = D * A) (hBC : B * C = C * B) (hBD : B * D = D * B) :
    (Matrix.fromBlocks A B (-B) A) * (Matrix.fromBlocks C D (-D) C) =
      (Matrix.fromBlocks C D (-D) C) * (Matrix.fromBlocks A B (-B) A) := by
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  have e11 : A * C + B * (-D) = C * A + D * (-B) := by
    rw [Matrix.mul_neg, Matrix.mul_neg, hAC, hBD]
  have e12 : A * D + B * C = C * B + D * A := by rw [hAD, hBC]; abel
  have e21 : (-B) * C + A * (-D) = (-D) * A + C * (-B) := by
    rw [Matrix.neg_mul, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_neg, hBC, hAD]; abel
  have e22 : (-B) * D + A * C = (-D) * B + C * A := by
    rw [Matrix.neg_mul, Matrix.neg_mul, hBD, hAC]
  rw [e11, e12, e21, e22]

/-- **W2. Williamson's array.** Four symmetric, pairwise commuting `±1` matrices whose
squares sum to `4n · I` assemble into a Hadamard matrix of order `4n`. -/
theorem solution (A B C D : Matrix ι ι ℝ)
    (hApm : ∀ i j, A i j = 1 ∨ A i j = -1) (hBpm : ∀ i j, B i j = 1 ∨ B i j = -1)
    (hCpm : ∀ i j, C i j = 1 ∨ C i j = -1) (hDpm : ∀ i j, D i j = 1 ∨ D i j = -1)
    (hAs : Aᵀ = A) (hBs : Bᵀ = B) (hCs : Cᵀ = C) (hDs : Dᵀ = D)
    (hAB : A * B = B * A) (hAC : A * C = C * A) (hAD : A * D = D * A)
    (hBC : B * C = C * B) (hBD : B * D = D * B) (hCD : C * D = D * C)
    (hsum : A * A + B * B + C * C + D * D =
      ((4 * Fintype.card ι : ℕ) : ℝ) • (1 : Matrix ι ι ℝ)) :
    ∃ M : Matrix ((ι ⊕ ι) ⊕ (ι ⊕ ι)) ((ι ⊕ ι) ⊕ (ι ⊕ ι)) ℝ,
      (∀ i j, M i j = 1 ∨ M i j = -1) ∧
        M * Mᵀ = ((4 * Fintype.card ι : ℕ) : ℝ) •
          (1 : Matrix ((ι ⊕ ι) ⊕ (ι ⊕ ι)) ((ι ⊕ ι) ⊕ (ι ⊕ ι)) ℝ) := by
  set P : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ := Matrix.fromBlocks A B (-B) A with hPdef
  set Q : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ := Matrix.fromBlocks C D (-D) C with hQdef
  refine ⟨Matrix.fromBlocks P Q (-Qᵀ) Pᵀ, ?_, ?_⟩
  · -- entries are ±1
    have hPpm : ∀ i j, P i j = 1 ∨ P i j = -1 := by
      rw [hPdef]; exact fromBlocks_pm A B (-B) A hApm hBpm (neg_pm B hBpm) hApm
    have hQpm : ∀ i j, Q i j = 1 ∨ Q i j = -1 := by
      rw [hQdef]; exact fromBlocks_pm C D (-D) C hCpm hDpm (neg_pm D hDpm) hCpm
    exact fromBlocks_pm P Q (-Qᵀ) Pᵀ hPpm hQpm
      (neg_pm Qᵀ (transpose_pm Q hQpm)) (transpose_pm P hPpm)
  · -- orthogonality
    have hPPt : P * Pᵀ = Matrix.fromBlocks (A * A + B * B) 0 0 (A * A + B * B) := by
      rw [hPdef]; exact block_complex_mul_transpose A B hAs hBs hAB
    have hQQt : Q * Qᵀ = Matrix.fromBlocks (C * C + D * D) 0 0 (C * C + D * D) := by
      rw [hQdef]; exact block_complex_mul_transpose C D hCs hDs hCD
    have hPtP : Pᵀ * P = Matrix.fromBlocks (A * A + B * B) 0 0 (A * A + B * B) := by
      rw [hPdef]; exact block_complex_transpose_mul A B hAs hBs hAB
    have hQtQ : Qᵀ * Q = Matrix.fromBlocks (C * C + D * D) 0 0 (C * C + D * D) := by
      rw [hQdef]; exact block_complex_transpose_mul C D hCs hDs hCD
    have hPQ : P * Q = Q * P := by
      rw [hPdef, hQdef]; exact block_complex_comm A B C D hAC hAD hBC hBD
    have hWt : (Matrix.fromBlocks P Q (-Qᵀ) Pᵀ)ᵀ = Matrix.fromBlocks Pᵀ (-Q) Qᵀ P := by
      rw [Matrix.fromBlocks_transpose, Matrix.transpose_neg, Matrix.transpose_transpose,
        Matrix.transpose_transpose]
    rw [hWt, Matrix.fromBlocks_multiply]
    have e12 : P * (-Q) + Q * P = 0 := by rw [Matrix.mul_neg, hPQ]; abel
    have e21 : (-Qᵀ) * Pᵀ + Pᵀ * Qᵀ = 0 := by
      rw [Matrix.neg_mul, ← Matrix.transpose_mul, ← Matrix.transpose_mul, hPQ]; abel
    have e22 : (-Qᵀ) * (-Q) + Pᵀ * P = P * Pᵀ + Q * Qᵀ := by
      rw [neg_mul_neg, hQtQ, hPtP, hPPt, hQQt]; abel
    rw [e12, e21, e22]
    have hdiag : P * Pᵀ + Q * Qᵀ =
        ((4 * Fintype.card ι : ℕ) : ℝ) • (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) ℝ) := by
      rw [hPPt, hQQt, Matrix.fromBlocks_add, add_zero]
      have hs : A * A + B * B + (C * C + D * D) =
          ((4 * Fintype.card ι : ℕ) : ℝ) • (1 : Matrix ι ι ℝ) := by
        rw [← hsum]; abel
      rw [hs, fromBlocks_smul_one]
    rw [hdiag, fromBlocks_smul_one]
