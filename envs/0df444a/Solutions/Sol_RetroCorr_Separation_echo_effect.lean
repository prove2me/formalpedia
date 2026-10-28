-- Prove2me | solution 1 for RetroCorr.Separation.echo_effect
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T03:25:08.922035+00:00
-- url     : https://prove2.me/submissions/91f3b406-55b6-480f-826f-9fca09705d15

import Mathlib
import Definitions.Def_RetroCorr_Separation_Channel

open RetroCorr.Separation

theorem solution (c : ℕ) (W : Matrix.unitaryGroup (Fin c) ℂ) (i j : Fin c) :
    QAlgorithms.effectProb (Matrix.kronecker (transposeBasisProj W i) (basisProj W j))
      (maxEntDensity c) = if i = j then ((c : ℝ))⁻¹ else 0 := by
  have hU : star (W : Matrix (Fin c) (Fin c) ℂ) * (W : Matrix (Fin c) (Fin c) ℂ) = 1 :=
    Matrix.mem_unitaryGroup_iff'.mp W.2
  set M : Matrix (Fin c) (Fin c) ℂ := (W : Matrix (Fin c) (Fin c) ℂ) with hM
  have key : (Matrix.kronecker (transposeBasisProj W i) (basisProj W j) * maxEntDensity c).trace
      = (c : ℂ)⁻¹ * ((star M * M) j i * star ((star M * M) j i)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fintype.sum_prod_type,
      maxEntDensity, Matrix.of_apply, Matrix.kroneckerMap_apply, Matrix.kronecker,
      transposeBasisProj, basisProj, Matrix.transpose_apply, Matrix.star_apply]
    simp only [ite_and, ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_ite_irrel, Finset.sum_const_zero]
    rw [hM]
    simp only [star_sum, star_mul, star_star, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [QAlgorithms.effectProb, key, hU]
  by_cases h : i = j
  · subst h
    simp
  · rw [if_neg h, Matrix.one_apply_ne (Ne.symm h)]
    simp
