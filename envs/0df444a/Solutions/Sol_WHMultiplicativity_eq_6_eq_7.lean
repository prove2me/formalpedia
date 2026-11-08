-- Prove2me | solution 1 for WHMultiplicativity.eq_6_eq_7
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T22:09:31.832666+00:00
-- url     : https://prove2.me/submissions/0a2d04a9-b82e-4f66-acc9-b643185b3fd3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_WHAdditivity_Renyi_Model

open scoped Matrix
open WHAdditivity.Renyi

theorem solution (d : ℕ) (hd : 2 ≤ d) (X : Matrix (Fin d) (Fin d) ℂ) :
    wernerHolevo d X =
      (2 * ((d : ℂ) - 1))⁻¹ • ∑ i : Fin d, ∑ j : Fin d,
        (Matrix.single i j (1 : ℂ) - Matrix.single j i 1)ᴴ * X *
          (Matrix.single i j (1 : ℂ) - Matrix.single j i 1) := by
  have h4 : ∀ i j : Fin d,
      (Matrix.single i j (1 : ℂ) - Matrix.single j i 1)ᴴ * X *
          (Matrix.single i j (1 : ℂ) - Matrix.single j i 1) =
        Matrix.single j j (X i i) - Matrix.single j i (X i j) - Matrix.single i j (X j i) +
          Matrix.single i i (X j j) := by
    intro i j
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_single, star_one, sub_mul, mul_sub,
      Matrix.single_mul_mul_single, one_mul, mul_one]
    abel
  have hT1 : ∀ c : ℂ, ∑ j : Fin d, Matrix.single j j c = c • (1 : Matrix (Fin d) (Fin d) ℂ) := by
    intro c
    rw [Matrix.sum_single_eq_diagonal]
    ext p q
    simp [Matrix.diagonal_apply, Matrix.one_apply]
  have hT2 : ∑ i : Fin d, ∑ j : Fin d, Matrix.single i j (X j i) = Xᵀ := by
    rw [Matrix.sum_sum_single]
    ext p q
    simp
  have hT3 : ∑ i : Fin d, ∑ j : Fin d, Matrix.single j i (X i j) = Xᵀ := by
    rw [Finset.sum_comm]
    exact hT2
  have hT4 : ∑ i : Fin d, ∑ j : Fin d, Matrix.single j j (X i i) =
      X.trace • (1 : Matrix (Fin d) (Fin d) ℂ) := by
    rw [Finset.sum_congr rfl (fun i _ => hT1 (X i i)), ← Finset.sum_smul]
    rfl
  have hT5 : ∑ i : Fin d, ∑ j : Fin d, Matrix.single i i (X j j) =
      X.trace • (1 : Matrix (Fin d) (Fin d) ℂ) := by
    rw [Finset.sum_comm]
    exact hT4
  rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => h4 i j))]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hT4, hT3, hT2, hT5]
  have hd1 : (d : ℂ) - 1 ≠ 0 := by
    intro h
    have h' : (d : ℂ) = 1 := sub_eq_zero.mp h
    norm_cast at h'
    omega
  unfold wernerHolevo
  ext p q
  simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.one_apply,
    Matrix.transpose_apply, smul_eq_mul]
  split_ifs <;> field_simp <;> ring
