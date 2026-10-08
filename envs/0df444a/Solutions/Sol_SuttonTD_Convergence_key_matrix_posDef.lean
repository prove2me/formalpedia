-- Prove2me | solution 1 for SuttonTD.Convergence.key_matrix_posDef
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T04:33:11.877124+00:00
-- url     : https://prove2.me/submissions/07e43d99-04c6-4a08-9f4b-83cac2de45dd

import Mathlib
import Definitions.Def_SuttonTD_Convergence_AbsorbingChain
import Definitions.Def_SuttonTD_Convergence_IsPosDefReal

set_option autoImplicit false

open Matrix SuttonTD.Convergence in
theorem solution {N T : Type*} [Fintype N] [DecidableEq N] [Fintype T]
    (C : AbsorbingChain N T) (μ : N → ℝ) (hμ0 : ∀ i, 0 ≤ μ i) (hμ1 : ∑ i, μ i = 1)
    (hd : ∀ i, 0 < (μ ᵥ* (1 - C.Q)⁻¹) i) :
    IsPosDefReal (diagonal (μ ᵥ* (1 - C.Q)⁻¹) * (1 - C.Q)) := by
  intro y hy
  set M : Matrix N N ℝ := 1 - C.Q with hMdef
  set d : N → ℝ := μ ᵥ* M⁻¹ with hddef
  set Q : Matrix N N ℝ := C.Q with hQdef
  obtain ⟨i0, hi0⟩ := Function.ne_iff.mp hy
  -- invertibility of M
  have hdet : IsUnit M.det := by
    by_contra hnu
    have h0 : M⁻¹ = 0 := Matrix.nonsing_inv_apply_not_isUnit M hnu
    have := hd i0
    rw [hddef, h0] at this
    simp at this
  have hdM : d ᵥ* M = μ := by
    rw [hddef, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]
  have hcol : ∀ j, d j - ∑ i, d i * Q i j = μ j := by
    intro j
    have := congrFun hdM j
    rw [hMdef, Matrix.vecMul_sub, Matrix.vecMul_one] at this
    simpa [Matrix.vecMul, dotProduct] using this
  have hQnn : ∀ i j, 0 ≤ Q i j := fun i j => by
    simp [hQdef, AbsorbingChain.Q, C.pN_nonneg]
  have hrow : ∀ i, ∑ j, Q i j ≤ 1 := fun i => by
    have h1 := C.row_sum i
    have h2 : 0 ≤ ∑ j, C.pT i j := Finset.sum_nonneg (fun j _ => C.pT_nonneg i j)
    have h3 : ∑ j, Q i j = ∑ j, C.pN i j := by simp [hQdef, AbsorbingChain.Q]
    linarith
  have hdpos : ∀ i, 0 < d i := hd
  -- the form
  have hform : y ⬝ᵥ ((diagonal d * M) *ᵥ y)
      = ∑ i, y i * (d i * (y i - ∑ j, Q i j * y j)) := by
    rw [← Matrix.mulVec_mulVec, hMdef, Matrix.sub_mulVec, Matrix.one_mulVec]
    simp only [dotProduct, Matrix.mulVec_diagonal, Pi.sub_apply]
    simp [Matrix.mulVec, dotProduct]
  have eF : ∑ i, y i * (d i * (y i - ∑ j, Q i j * y j))
      = ∑ i, d i * y i ^ 2 - ∑ i, ∑ j, d i * y i * (Q i j * y j) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.mul_sum]; ring
  have eB : ∑ i, d i * (1 - ∑ j, Q i j) * y i ^ 2
      = ∑ i, d i * y i ^ 2 - ∑ i, ∑ j, d i * Q i j * y i ^ 2 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_mul, ← Finset.mul_sum]; ring
  have eR : ∑ i, ∑ j, d i * Q i j * y j ^ 2 = ∑ j, (∑ i, d i * Q i j) * y j ^ 2 := by
    rw [Finset.sum_comm]; simp only [Finset.sum_mul]
  have eC : ∑ j, μ j * y j ^ 2
      = ∑ j, d j * y j ^ 2 - ∑ i, ∑ j, d i * Q i j * y j ^ 2 := by
    rw [eR, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← hcol j]; ring
  have eA : ∑ i, ∑ j, d i * Q i j * (y i - y j) ^ 2
      = ∑ i, ∑ j, d i * Q i j * y i ^ 2 - 2 * ∑ i, ∑ j, d i * y i * (Q i j * y j)
        + ∑ i, ∑ j, d i * Q i j * y j ^ 2 := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  have hAnn : 0 ≤ ∑ i, ∑ j, d i * Q i j * (y i - y j) ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (hdpos i).le (hQnn i j)) (sq_nonneg _)
  have hBnn : 0 ≤ ∑ i, d i * (1 - ∑ j, Q i j) * y i ^ 2 :=
    Finset.sum_nonneg fun i _ =>
      mul_nonneg (mul_nonneg (hdpos i).le (by linarith [hrow i])) (sq_nonneg _)
  have hCnn : 0 ≤ ∑ j, μ j * y j ^ 2 :=
    Finset.sum_nonneg fun j _ => mul_nonneg (hμ0 j) (sq_nonneg _)
  rw [hform, eF]
  by_contra hle
  push Not at hle
  have hA0 : ∑ i, ∑ j, d i * Q i j * (y i - y j) ^ 2 = 0 := by linarith
  have hB0 : ∑ i, d i * (1 - ∑ j, Q i j) * y i ^ 2 = 0 := by linarith
  have hAterm : ∀ i j, d i * Q i j * (y i - y j) ^ 2 = 0 := by
    intro i j
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (hdpos i).le (hQnn i j)) (sq_nonneg (y i - y j)))).mp hA0 i
      (Finset.mem_univ _)
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ =>
      mul_nonneg (mul_nonneg (hdpos i).le (hQnn i j)) (sq_nonneg (y i - y j)))).mp h1 j
      (Finset.mem_univ _)
  have hBterm : ∀ i, d i * (1 - ∑ j, Q i j) * y i ^ 2 = 0 := by
    intro i
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
      mul_nonneg (mul_nonneg (hdpos i).le (by linarith [hrow i])) (sq_nonneg (y i)))).mp hB0 i
      (Finset.mem_univ _)
  have hMy : M *ᵥ y = 0 := by
    funext i
    have hs : ∑ j, Q i j * y j = (∑ j, Q i j) * y i := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rcases mul_eq_zero.mp (hAterm i j) with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' (hdpos i).ne'
        · simp [h']
      · have h2 : y i - y j = 0 := (pow_eq_zero_iff two_ne_zero).mp h
        rw [sub_eq_zero.mp h2]
    rw [hMdef, Matrix.sub_mulVec, Matrix.one_mulVec]
    simp only [Pi.sub_apply, Pi.zero_apply, Matrix.mulVec, dotProduct]
    rw [hs]
    rcases mul_eq_zero.mp (hBterm i) with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact absurd h' (hdpos i).ne'
      · linear_combination (y i) * h'
    · have h2 : y i = 0 := (pow_eq_zero_iff two_ne_zero).mp h
      simp [h2]
  have hy0 : y = 0 := by
    have := congrArg (fun v => M⁻¹ *ᵥ v) hMy
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet] using this
  exact hy hy0
