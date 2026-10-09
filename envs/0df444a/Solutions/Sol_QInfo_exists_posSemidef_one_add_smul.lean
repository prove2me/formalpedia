-- Prove2me | solution 1 for QInfo.exists_posSemidef_one_add_smul
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-08T23:31:36.891748+00:00
-- url     : https://prove2.me/submissions/4f7b2e99-ff86-49dc-843c-2d33e5dde8f8

import Mathlib

open Matrix
open scoped ComplexOrder

theorem solution {n : Type*} [Fintype n] [DecidableEq n] (H : Matrix n n ℂ) (hH : H.IsHermitian) :
    ∃ t : ℝ, 0 < t ∧ (1 + (t : ℂ) • H).PosSemidef := by
  set U : Matrix n n ℂ := (hH.eigenvectorUnitary : Matrix n n ℂ)
  set ev := hH.eigenvalues
  set t : ℝ := 1 / (1 + ∑ i, |ev i|)
  have hS : 0 ≤ ∑ i, |ev i| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have ht : 0 < t := by positivity
  refine ⟨t, ht, ?_⟩
  have hUU : U * star U = 1 := Unitary.coe_mul_star_self _
  have hspec : H = U * diagonal (RCLike.ofReal ∘ ev) * star U := by
    have := hH.spectral_theorem; rwa [Unitary.conjStarAlgAut_apply] at this
  have heq : 1 + (t : ℂ) • H =
      U * diagonal (fun i => ((1 + t * ev i : ℝ) : ℂ)) * star U := by
    have : diagonal (fun i => ((1 + t * ev i : ℝ) : ℂ)) =
        1 + (t : ℂ) • diagonal (RCLike.ofReal ∘ ev) := by
      ext i j; by_cases h : i = j <;> simp [diagonal_apply, h, one_apply]
    rw [this, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hUU, Matrix.mul_smul,
      Matrix.smul_mul, ← hspec]
  rw [heq, star_eq_conjTranspose]
  refine PosSemidef.mul_mul_conjTranspose_same ?_ U
  refine posSemidef_diagonal_iff.mpr fun i => Complex.zero_le_real.mpr ?_
  have h1 : |ev i| ≤ ∑ j, |ev j| :=
    Finset.single_le_sum (f := fun j => |ev j|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have h2 : t * |ev i| < 1 := by
    rw [show t = 1 / (1 + ∑ j, |ev j|) from rfl, div_mul_eq_mul_div, one_mul,
      div_lt_one (by positivity)]
    linarith
  have h3 : -(t * |ev i|) ≤ t * ev i := by
    rw [← mul_neg]; exact mul_le_mul_of_nonneg_left (neg_abs_le _) ht.le
  linarith
