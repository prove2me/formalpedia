-- Prove2me | solution 1 for ShiShallow.acceptOperator_isHermitian
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-13T22:25:26.117218+00:00
-- url     : https://prove2.me/submissions/8e8bd695-cc04-44d8-84c7-1899ac7dd6b7

/-
Copyright (c) 2026 Yueheng Shi. All rights reserved.
Released under the Apache License, Version 2.0.
Authors: Yueheng Shi
-/
import Definitions.Def_ShiShallow_Matrix

set_option autoImplicit false

open ShiShallow

/-! ### The output projector: entries -/

private lemma accH_entry {n : ℕ} (out : Fin n) (y z : Bits n) :
    projOut out y z = if y = z ∧ y out = true then 1 else 0 := by
  first
  | rfl
  | (simp only [projOut, Matrix.of_apply]; done)
  | (simp [projOut]; done)

/-! ### `star` of a real 0/1 indicator is itself -/

private lemma accH_star_ite (c : Prop) [Decidable c] :
    star (if c then (1 : ℂ) else 0) = if c then (1 : ℂ) else 0 := by
  by_cases h : c
  · rw [if_pos h, star_one]
  · rw [if_neg h, star_zero]

/-! ### The diagonal guard is symmetric in its two indices -/

private lemma accH_diag_symm {n : ℕ} (out : Fin n) (y z : Bits n) :
    (if z = y ∧ z out = true then (1 : ℂ) else 0)
      = (if y = z ∧ y out = true then (1 : ℂ) else 0) := by
  by_cases h : y = z
  · rw [h]
  · have h1 : ¬(z = y ∧ z out = true) := by
      intro hc
      exact h hc.1.symm
    have h2 : ¬(y = z ∧ y out = true) := by
      intro hc
      exact h hc.1
    rw [if_neg h1, if_neg h2]

/-! ### ACC-1's Hermitian half, re-proved here in `star` form -/

private lemma accH_projOut_star {n : ℕ} (out : Fin n) :
    star (projOut out) = projOut out := by
  ext y z
  first
  | (simp only [Matrix.star_apply])
  | (simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply])
  rw [accH_entry out z y, accH_star_ite, accH_entry out y z]
  exact accH_diag_symm out y z

private lemma accH_projOut_herm {n : ℕ} (out : Fin n) :
    (projOut out).conjTranspose = projOut out := by
  rw [← Matrix.star_eq_conjTranspose]
  exact accH_projOut_star out

/-! ### The registered statement: conjugation preserves Hermitian-ness -/

theorem solution {n : ℕ} (A : Op n) (out : Fin n) :
    (star A * projOut out * A).IsHermitian := by
  have hP : star (projOut out) = projOut out := accH_projOut_star out
  have hPh : (projOut out).conjTranspose = projOut out := accH_projOut_herm out
  show (star A * projOut out * A).conjTranspose = star A * projOut out * A
  first
  | (rw [← Matrix.star_eq_conjTranspose, star_mul, star_mul, star_star, hP, mul_assoc]; done)
  | (rw [Matrix.star_eq_conjTranspose A, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
         Matrix.conjTranspose_conjTranspose, hPh, mul_assoc]; done)
  | (rw [← Matrix.star_eq_conjTranspose, star_mul, star_mul, star_star, hP, Matrix.mul_assoc]
     done)
  | (rw [← Matrix.star_eq_conjTranspose, star_mul, star_mul, star_star, hP]
     rw [mul_assoc]
     done)
