-- Prove2me | solution 1 for WeilDefect.RPB108.scaled_gram_difference
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T03:59:52.119993+00:00
-- url     : https://prove2.me/submissions/a4b967e8-77e7-4fb2-8029-de04d5a5aeb1

import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem solution (V G : Fin 3 → Fin 3 → ℝ) (s : Fin 3 → ℝ)
    (rho : ℝ) (z : Fin 3 → ℂ) :
    complexGram (fun i j => s i*s j*(rho*V i j-G i j)) z =
      rho*complexGram V (fun i => (s i : ℂ)*z i)-
        complexGram G (fun i => (s i : ℂ)*z i) := by
  simp only [complexGram, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp [Complex.mul_re, Complex.mul_im]
  ring
