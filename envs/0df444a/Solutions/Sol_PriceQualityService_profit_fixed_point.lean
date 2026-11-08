-- Prove2me | solution 1 for PriceQualityService.profit_fixed_point
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:31:22.235015+00:00
-- url     : https://prove2.me/submissions/799617f5-1477-4f64-b347-b8df3dcd1326

import Mathlib
import Definitions.Def_PriceQualityService_profit

open PriceQualityService in
theorem solution {N : ℕ} (α s a b c p q t : Fin N → ℝ) :
    profit α s a b c p q t =
      ∑ i, (margin a b c p q t i - profit α s a b c p q t) * Real.exp (utility α s p q t i) := by
  have hD : 0 < 1 + ∑ j, Real.exp (utility α s p q t j) := by
    have : 0 ≤ ∑ j, Real.exp (utility α s p q t j) :=
      Finset.sum_nonneg (fun j _ => (Real.exp_pos _).le)
    linarith
  have hp : profit α s a b c p q t * (1 + ∑ j, Real.exp (utility α s p q t j)) =
      ∑ i, margin a b c p q t i * Real.exp (utility α s p q t i) := by
    unfold profit choiceProb
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [mul_assoc, div_mul_cancel₀ _ hD.ne']
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  linear_combination hp
