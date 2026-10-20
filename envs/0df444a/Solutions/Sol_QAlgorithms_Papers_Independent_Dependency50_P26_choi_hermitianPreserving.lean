-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P26.choi_hermitianPreserving
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:52:17.63972+00:00
-- url     : https://prove2.me/submissions/b61ca561-804e-4294-ae02-550079b7d01b

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P26

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms

attribute [local instance] Classical.decEq Classical.propDecidable

open QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P26

theorem g52b_choi_apply {I O : Type*} [Fintype I] (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (o o' : O) (i i' : I) :
    outputFirstChoi M (o, i) (o', i') = M (Matrix.single i i' 1) o o' := rfl

theorem g52b_lin_expand {I O : Type*} [Fintype I] (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (X : Matrix I I ℂ) : M X = ∑ i, ∑ j, X i j • M (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single X]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

theorem g52b_hp_adj {I O : Type*} [Fintype I] (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ)
    (h : HermitianPreserving M) (X : Matrix I I ℂ) : (M X)ᴴ = M Xᴴ := by
  obtain ⟨H, hHdef⟩ : ∃ H : Matrix I I ℂ, H = (1/2 : ℂ) • (X + Xᴴ) := ⟨_, rfl⟩
  obtain ⟨K, hKdef⟩ : ∃ K : Matrix I I ℂ, K = (-(Complex.I / 2)) • (X - Xᴴ) := ⟨_, rfl⟩
  have hHh : H.IsHermitian := by
    rw [Matrix.IsHermitian, hHdef, Matrix.conjTranspose_smul, Matrix.conjTranspose_add,
      Matrix.conjTranspose_conjTranspose, add_comm]
    congr 1; simp
  have hKh : K.IsHermitian := by
    have hs : star (-(Complex.I / 2)) = Complex.I / 2 := by simp [Complex.conj_I, neg_div]
    rw [Matrix.IsHermitian, hKdef, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_conjTranspose, hs, ← neg_sub, smul_neg, ← neg_smul]
  have e1 : X = H + Complex.I • K := by
    ext a b
    rw [hHdef, hKdef]
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.conjTranspose_apply]
    linear_combination ((X a b - star (X b a)) / 2) * Complex.I_sq
  have e2 : Xᴴ = H - Complex.I • K := by
    ext a b
    rw [hHdef, hKdef]
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.conjTranspose_apply]
    linear_combination (-(X a b - star (X b a)) / 2) * Complex.I_sq
  have hMH := h H hHh
  have hMK := h K hKh
  rw [e2, e1, map_add, map_smul, map_sub, map_smul, Matrix.conjTranspose_add,
    Matrix.conjTranspose_smul, hMH.eq, hMK.eq]
  simp [Complex.conj_I, sub_eq_add_neg]

/-- PDF p.2, Lemma 2. -/
theorem solution {I O : Type*} [Fintype I] [Fintype O]
    [Nonempty I] [Nonempty O] (M : Matrix I I ℂ →ₗ[ℂ] Matrix O O ℂ) :
    HermitianPreserving M ↔ (outputFirstChoi M).IsHermitian := by
  constructor
  · intro h
    ext ⟨o, i⟩ ⟨o', i'⟩
    rw [Matrix.conjTranspose_apply, g52b_choi_apply, g52b_choi_apply]
    have := congrFun (congrFun (g52b_hp_adj M h (Matrix.single i' i 1)) o) o'
    rw [Matrix.conjTranspose_apply] at this
    rw [this, Matrix.conjTranspose_single, star_one]
  · intro h X hX
    have hd : ∀ i i', (M (Matrix.single i i' 1))ᴴ = M (Matrix.single i' i 1) := by
      intro i i'
      ext o o'
      rw [Matrix.conjTranspose_apply]
      have := congrArg (fun A : Matrix (O × I) (O × I) ℂ => A (o, i') (o', i)) h.eq
      rw [Matrix.conjTranspose_apply, g52b_choi_apply, g52b_choi_apply] at this
      exact this
    have hx : ∀ i j, star (X i j) = X j i := fun i j => hX.apply j i
    show (M X)ᴴ = M X
    rw [g52b_lin_expand M X, Matrix.conjTranspose_sum]
    simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, hd, hx]
    exact Finset.sum_comm


end

