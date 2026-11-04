-- Prove2me | solution 1 for PriceQualityService.yValue_convex
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-03T12:29:39.136207+00:00
-- url     : https://prove2.me/submissions/b7d9e886-c814-40ae-aa93-2997ac1a65b4

import Definitions.Def_PriceQualityService_yValue
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

open PriceQualityService

theorem solution {N : ℕ} (α s a b c q : Fin N → ℝ) :
    ConvexOn ℝ Set.univ (fun t : ℝ => yValue α s a b c q (fun _ => t)) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy A B hA hB hAB
  change (∑ i, Real.exp (netValue α s a b c q (fun _ => A*x+B*y) i)) ≤
    A * (∑ i, Real.exp (netValue α s a b c q (fun _ => x) i)) +
    B * (∑ i, Real.exp (netValue α s a b c q (fun _ => y) i))
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hc := convexOn_exp.2 (Set.mem_univ (netValue α s a b c q (fun _ => x) i))
    (Set.mem_univ (netValue α s a b c q (fun _ => y) i)) hA hB hAB
  simp only [smul_eq_mul] at hc
  convert hc using 1
  congr 1
  dsimp only [netValue]
  linear_combination -(α i * q i - c i * q i ^ 2) * hAB

#print axioms solution

