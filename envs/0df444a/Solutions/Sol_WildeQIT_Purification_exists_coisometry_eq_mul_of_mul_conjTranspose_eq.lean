-- Prove2me | solution 1 for WildeQIT.Purification.exists_coisometry_eq_mul_of_mul_conjTranspose_eq
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-11-06T19:42:40.646544+00:00
-- url     : https://prove2.me/submissions/4c8b7b61-49ed-4973-8f7c-612ee53b2dec

import Mathlib
import Theorems.Thm_WildeQIT_Purification_exists_unitary_eq_mul_of_mul_conjTranspose_eq

open Matrix WildeQIT.Purification

theorem solution {a m n : Type*} [Fintype a] [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (A : Matrix a m ℂ) (B : Matrix a n ℂ) (hcard : Fintype.card n ≤ Fintype.card m)
    (h : A * Aᴴ = B * Bᴴ) :
    ∃ V : Matrix n m ℂ, V * Vᴴ = 1 ∧ A = B * V := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let J : Matrix m n ℂ := Matrix.of fun i j => if i = e j then 1 else 0
  have hJ : Jᴴ * J = 1 := by
    ext j j'
    simp only [J, Matrix.mul_apply, conjTranspose_apply, of_apply, Matrix.one_apply]
    simp only [apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, e.injective.eq_iff]
  have h' : A * Aᴴ = (B * Jᴴ) * (B * Jᴴ)ᴴ := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc Jᴴ, hJ, Matrix.one_mul, h]
  obtain ⟨W, hW, hAW⟩ := exists_unitary_eq_mul_of_mul_conjTranspose_eq A (B * Jᴴ) h'
  have hWW : W * star W = 1 := Matrix.mem_unitaryGroup_iff.mp hW
  refine ⟨Jᴴ * W, ?_, by rw [hAW, Matrix.mul_assoc]⟩
  rw [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc,
    ← Matrix.mul_assoc W, ← star_eq_conjTranspose, hWW, Matrix.one_mul, hJ]
