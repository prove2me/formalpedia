-- Prove2me | solution 1 for SupplyChainTheory.cs_stage1_newsvendor
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-26T21:11:16.267749+00:00
-- url     : https://prove2.me/submissions/63255748-9bec-4d31-aefe-5efa9c7aa43c

import Mathlib
import Definitions.Def_SupplyChainTheory_multiechelon

set_option autoImplicit false

open SupplyChainTheory in
/-- `h'₁ = h₁ + h'₂` when `N ≥ 1`. -/
lemma sct_localHolding_one_d620b344 (N : ℕ) (h : ℕ → ℝ) (hN : 1 ≤ N) :
    localHolding N h 1 = h 1 + localHolding N h 2 := by
  unfold localHolding
  rw [← Finset.add_sum_Ioc_eq_sum_Icc hN]
  rfl

open SupplyChainTheory in
theorem solution (N : ℕ) (h : ℕ → ℝ) (p : ℝ) (D : ℕ → MeasureTheory.Measure ℝ)
    (S : ℕ → ℝ) (hN : 1 ≤ N) [MeasureTheory.IsProbabilityMeasure (D 1)]
    (hD : MeasureTheory.Integrable (fun x => x) (D 1)) (y : ℝ) :
    csG N h p D S 1 y
      = ∫ d, (h 1 * max (y - d) 0 + (p + localHolding N h 2) * max (d - y) 0) ∂(D 1) := by
  unfold csG
  apply MeasureTheory.integral_congr_ae
  refine Filter.Eventually.of_forall (fun d => ?_)
  simp only [csHat, csBar, Nat.sub_self]
  rw [sct_localHolding_one_d620b344 N h hN]
  have hneg : -(y - d) = d - y := by ring
  rw [hneg]
  rcases le_total d y with hdy | hdy
  · rw [max_eq_left (by linarith : (0:ℝ) ≤ y - d), max_eq_right (by linarith : d - y ≤ 0)]
    ring
  · rw [max_eq_right (by linarith : y - d ≤ 0), max_eq_left (by linarith : (0:ℝ) ≤ d - y)]
    ring
