-- Prove2me | solution 1 for VectorSpaceOpt.dual_approximation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-26T13:06:24.333327+00:00
-- url     : https://prove2.me/submissions/97f27099-cf81-4f68-adc6-5675a062e47d

import Mathlib
open scoped RealInnerProductSpace


theorem solution {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    {n : ℕ} (y : Fin n → H) (hy : LinearIndependent ℝ y) (c : Fin n → ℝ) :
    ∃ β : Fin n → ℝ,
      (∀ i, ∑ j, β j * ⟪y j, y i⟫ = c i) ∧
      (∀ i, ⟪∑ j, β j • y j, y i⟫ = c i) ∧
      (∀ z : H, (∀ i, ⟪z, y i⟫ = c i) → ‖∑ j, β j • y j‖ ≤ ‖z‖) ∧
      (∀ z : H, (∀ i, ⟪z, y i⟫ = c i) → ‖z‖ ≤ ‖∑ j, β j • y j‖ →
        z = ∑ j, β j • y j) := by
  classical
  set A : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j => ⟪y j, y i⟫ with hA
  have hAg : A = Matrix.of fun i j => ⟪y i, y j⟫ := by
    ext i j; rw [hA]; simp [real_inner_comm]
  have hdet : A.det ≠ 0 := by
    rw [hAg]
    exact Matrix.det_gram_ne_zero_iff_linearIndependent.2 hy
  set β : Fin n → ℝ := A⁻¹.mulVec c with hβ
  have hAβ : A.mulVec β = c := by
    rw [hβ, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.2 hdet),
      Matrix.one_mulVec]
  have h1 : ∀ i, ∑ j, β j * ⟪y j, y i⟫ = c i := by
    intro i
    have hi := congrFun hAβ i
    simp only [Matrix.mulVec, dotProduct, hA, Matrix.of_apply] at hi
    rw [← hi]
    exact Finset.sum_congr rfl fun j _ => by rw [mul_comm]
  set v : H := ∑ j, β j • y j with hv
  have h2 : ∀ i, ⟪v, y i⟫ = c i := by
    intro i
    rw [hv, sum_inner, ← h1 i]
    exact Finset.sum_congr rfl fun j _ => by rw [real_inner_smul_left]
  have hvmem : v ∈ Submodule.span ℝ (Set.range y) :=
    Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  have hkey : ∀ z : H, (∀ i, ⟪z, y i⟫ = c i) → ⟪z - v, v⟫ = 0 := by
    intro z hz
    have hgen : ∀ m ∈ Submodule.span ℝ (Set.range y), ⟪z - v, m⟫ = 0 := by
      intro m hm
      induction hm using Submodule.span_induction with
      | mem w hw =>
          obtain ⟨i, rfl⟩ := hw
          rw [inner_sub_left, hz i, h2 i, sub_self]
      | zero => simp
      | add p q _ _ hp hq => rw [inner_add_right, hp, hq]; ring
      | smul a p _ hp => rw [real_inner_smul_right, hp]; ring
    exact hgen v hvmem
  have hsq : ∀ z : H, (∀ i, ⟪z, y i⟫ = c i) → ‖z‖ ^ 2 = ‖v‖ ^ 2 + ‖z - v‖ ^ 2 := by
    intro z hz
    have hsplit : z = v + (z - v) := by abel
    have hinner : ⟪v, z - v⟫ = 0 := by rw [real_inner_comm]; exact hkey z hz
    calc ‖z‖ ^ 2 = ‖v + (z - v)‖ ^ 2 := by rw [← hsplit]
      _ = ‖v‖ ^ 2 + 2 * ⟪v, z - v⟫ + ‖z - v‖ ^ 2 := by rw [norm_add_sq_real]
      _ = ‖v‖ ^ 2 + ‖z - v‖ ^ 2 := by rw [hinner]; ring
  refine ⟨β, h1, h2, ?_, ?_⟩
  · intro z hz
    have := hsq z hz
    nlinarith [norm_nonneg z, norm_nonneg v, sq_nonneg ‖z - v‖]
  · intro z hz hle
    have hs := hsq z hz
    have hzero : ‖z - v‖ ^ 2 = 0 := by
      nlinarith [norm_nonneg z, norm_nonneg v, sq_nonneg ‖z - v‖]
    have : ‖z - v‖ = 0 := by nlinarith [norm_nonneg (z - v)]
    exact sub_eq_zero.1 (norm_eq_zero.1 this)
