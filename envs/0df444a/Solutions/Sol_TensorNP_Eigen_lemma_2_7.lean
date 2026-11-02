-- Prove2me | solution 1 for TensorNP.Eigen.lemma_2_7
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T18:33:22.807934+00:00
-- url     : https://prove2.me/submissions/fa590e05-91c2-4bb9-87b6-78d2028d12ef

import Definitions.Def_TensorNP_Eigen_Construction

open Matrix Finset TensorNP.Eigen

private def left {n : ℕ} (x : Fin (n+n) → ℝ) : Fin n → ℝ := fun i ↦ x (Fin.castAdd n i)
private def right {n : ℕ} (x : Fin (n+n) → ℝ) : Fin n → ℝ := fun i ↦ x (Fin.natAdd n i)

private lemma realblock {m n : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℚ)
    (x : Fin (n+n) → ℝ) (i : Fin m) :
    x ⬝ᵥ (castMatrices ℝ (realSplit A) (Fin.castAdd m i) *ᵥ x) =
    ∑ j, ∑ k, (left x j * (A i j k : ℝ) * left x k - right x j * (A i j k : ℝ) * right x k) := by
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_add, castMatrices, realSplit,
    Matrix.map_apply, Matrix.reindex_apply, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, Sum.elim_inl, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.zero_apply, Matrix.neg_apply, Rat.cast_neg, Rat.cast_zero, mul_zero, Finset.sum_const_zero,
    add_zero, zero_add, mul_neg, Finset.sum_neg_distrib, mul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, left, right]
  simp only [Finset.sum_const_zero, mul_zero, zero_mul, add_zero, zero_add, Finset.mul_sum,
    mul_neg, Finset.sum_neg_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_assoc, neg_mul, sub_eq_add_neg]

private lemma imagblock {m n : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℚ)
    (x : Fin (n+n) → ℝ) (i : Fin m) :
    x ⬝ᵥ (castMatrices ℝ (realSplit A) (Fin.natAdd m i) *ᵥ x) =
    ∑ j, ∑ k, (left x j * (A i j k : ℝ) * right x k + right x j * (A i j k : ℝ) * left x k) := by
  simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_add, castMatrices, realSplit,
    Matrix.map_apply, Matrix.reindex_apply, Matrix.submatrix_apply,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
    Sum.elim_inr, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, Rat.cast_zero,
    mul_zero, Finset.sum_const_zero, add_zero, zero_add, mul_neg, Finset.sum_neg_distrib,
    mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib, left, right]
  simp only [Finset.sum_const_zero, mul_zero, zero_mul, add_zero, zero_add, Finset.mul_sum,
    mul_neg, Finset.sum_neg_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib, mul_assoc]

private def toComplex {n : ℕ} (x : Fin (n+n) → ℝ) (i : Fin n) : ℂ :=
  ⟨left x i, right x i⟩

private lemma complexblock_re {m n : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℚ)
    (x : Fin (n+n) → ℝ) (i : Fin m) :
    (toComplex x ⬝ᵥ (castMatrices ℂ A i *ᵥ toComplex x)).re =
      ∑ j, ∑ k, (left x j * (A i j k : ℝ) * left x k - right x j * (A i j k : ℝ) * right x k) := by
  simp only [dotProduct, Matrix.mulVec, Complex.re_sum, Complex.mul_re, Complex.mul_im,
    castMatrices, Matrix.map_apply, Complex.ratCast_re, Complex.ratCast_im, mul_zero,
    zero_mul, sub_zero, add_zero, toComplex, Finset.mul_sum,
    Finset.sum_sub_distrib, mul_assoc]

private lemma complexblock_im {m n : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℚ)
    (x : Fin (n+n) → ℝ) (i : Fin m) :
    (toComplex x ⬝ᵥ (castMatrices ℂ A i *ᵥ toComplex x)).im =
      ∑ j, ∑ k, (left x j * (A i j k : ℝ) * right x k + right x j * (A i j k : ℝ) * left x k) := by
  simp only [dotProduct, Matrix.mulVec, Complex.im_sum, Complex.re_sum, Complex.mul_re, Complex.mul_im,
    castMatrices, Matrix.map_apply, Complex.ratCast_re, Complex.ratCast_im, mul_zero,
    zero_mul, sub_zero, add_zero, toComplex, Finset.mul_sum,
    Finset.sum_add_distrib, mul_assoc]

private def fromComplex {n : ℕ} (z : Fin n → ℂ) (i : Fin (n+n)) : ℝ :=
  Sum.elim (fun j ↦ (z j).re) (fun j ↦ (z j).im) (finSumFinEquiv.symm i)

private lemma to_from {n : ℕ} (z : Fin n → ℂ) : toComplex (fromComplex z) = z := by
  funext i
  apply Complex.ext <;> simp only [toComplex, fromComplex, left, right,
    finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_castAdd,
    Sum.elim_inl, Sum.elim_inr]

private lemma from_to {n : ℕ} (x : Fin (n+n) → ℝ) : fromComplex (toComplex x) = x := by
  funext i
  have h := finSumFinEquiv.apply_symm_apply i
  cases hs : finSumFinEquiv.symm i with
  | inl j =>
    have : Fin.castAdd n j = i := by simpa [hs] using h
    simp only [fromComplex, hs, Sum.elim_inl, toComplex, left]
    exact congrArg x this
  | inr j =>
    have : Fin.natAdd n j = i := by simpa [hs] using h
    simp only [fromComplex, hs, Sum.elim_inr, toComplex, right]
    exact congrArg x this

theorem solution {m n : ℕ} (A : Fin m → Matrix (Fin n) (Fin n) ℚ) :
    QuadSolvable (castMatrices ℝ (realSplit A)) ↔ QuadSolvable (castMatrices ℂ A) := by
  constructor
  · rintro ⟨x, hx, hq⟩
    refine ⟨toComplex x, ?_, ?_⟩
    · intro hz
      apply hx
      have h := congrArg fromComplex hz
      have h0 : fromComplex (0 : Fin n → ℂ) = 0 := by
        funext j
        cases hj : finSumFinEquiv.symm j <;> simp [fromComplex, hj]
      simpa [from_to, h0] using h
    · intro i
      apply Complex.ext
      · rw [complexblock_re, ← realblock, hq]
        rfl
      · rw [complexblock_im, ← imagblock, hq]
        rfl
  · rintro ⟨z, hz, hq⟩
    let x := fromComplex z
    have hzx : toComplex x = z := to_from z
    refine ⟨x, ?_, ?_⟩
    · intro hx
      apply hz
      have h := congrArg toComplex hx
      have h0 : toComplex (0 : Fin (n+n) → ℝ) = 0 := by
        funext j
        apply Complex.ext <;> simp [toComplex, left, right]
      simpa [x, to_from, h0] using h
    · intro j
      have h := finSumFinEquiv.apply_symm_apply j
      cases hs : finSumFinEquiv.symm j with
      | inl i =>
        have hj : Fin.castAdd m i = j := by simpa [hs] using h
        subst j
        rw [realblock, ← complexblock_re, hzx, hq]
        rfl
      | inr i =>
        have hj : Fin.natAdd m i = j := by simpa [hs] using h
        subst j
        rw [imagblock, ← complexblock_im, hzx, hq]
        rfl
