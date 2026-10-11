-- Prove2me | solution 1 for WeilDefect.RPB108.complex_gram_add_div
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T04:54:51.508891+00:00
-- url     : https://prove2.me/submissions/0086658c-45ff-4574-893e-4ebb46713a99

import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

theorem solution (V G : Fin 3 → Fin 3 → ℝ) (k : ℝ) (z : Fin 3 → ℂ) :
    complexGram (fun i j => V i j+G i j/k) z =
      complexGram V z+complexGram G z/k := by
  simp only [complexGram, add_mul, Finset.sum_add_distrib, Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring
