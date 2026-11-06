-- Prove2me | solution 1 for ProbabilityTheory.IsPositiveDefinite.cnd_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T21:48:37.917126+00:00
-- url     : https://prove2.me/submissions/ae6e90f5-f212-459d-947b-3a2e0e7130c9

import Mathlib.Data.Complex.Basic
import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Mathlib.Algebra.BigOperators.Ring.Finset

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ProbabilityTheory
open scoped BigOperators

theorem solution {g : ℝ → ℂ} (hg : IsPositiveDefinite g) :
    IsConditionallyNegativeDefinite (fun ξ => g ξ - 1) := by
  intro n ξ c hc
  show 0 ≤ (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * (g (ξ i - ξ j) - 1)).re
  have e : (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * (g (ξ i - ξ j) - 1))
      = (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * g (ξ i - ξ j))
        - (∑ i, ∑ j, starRingEnd ℂ (c i) * c j) := by
    simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib]
  have hzero : (∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i) * c j) = 0 := by
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    simp [hc]
  rw [e, hzero, sub_zero]
  exact hg.re_nonneg n ξ c
