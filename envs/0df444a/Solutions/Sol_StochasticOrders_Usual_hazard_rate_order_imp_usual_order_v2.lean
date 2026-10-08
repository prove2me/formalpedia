-- Prove2me | solution 1 for StochasticOrders.Usual.hazard_rate_order_imp_usual_order_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T18:20:26.570242+00:00
-- url     : https://prove2.me/submissions/c0873f9c-1566-433a-b3c2-a0aaeba27cf2

import Mathlib
import Definitions.Def_StochasticOrders_Usual_UsualOrder
import Definitions.Def_StochasticOrders_Usual_HazardRateOrder

set_option autoImplicit false

open MeasureTheory Filter Topology in
lemma StochasticOrders.Usual.survival_neg_nat_tendsto_one_aux {Ω' : Type*} [MeasurableSpace Ω']
    (ν : Measure Ω') [IsProbabilityMeasure ν] (Y : Ω' → ℝ) :
    Tendsto (fun n : ℕ => ν {ω | -(n : ℝ) < Y ω}) atTop (𝓝 1) := by
  have hm : Monotone (fun n : ℕ => {ω | -(n : ℝ) < Y ω}) := by
    intro a b hab ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    linarith
  have hU : (⋃ n : ℕ, {ω | -(n : ℝ) < Y ω}) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    obtain ⟨n, hn⟩ := exists_nat_gt (-Y ω)
    exact ⟨n, by linarith⟩
  have := tendsto_measure_iUnion_atTop (μ := ν) hm
  rw [hU, measure_univ] at this
  exact this

open StochasticOrders.Usual MeasureTheory Filter Topology in
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (h : HazardRateOrder μ ν X Y) :
    UsualOrder μ ν X Y := by
  intro y
  have hT := StochasticOrders.Usual.survival_neg_nat_tendsto_one_aux ν Y
  have hL : Tendsto (fun n : ℕ => μ {ω | y < X ω} * ν {ω | -(n : ℝ) < Y ω}) atTop
      (𝓝 (μ {ω | y < X ω} * 1)) :=
    ENNReal.Tendsto.const_mul hT (Or.inl one_ne_zero)
  rw [mul_one] at hL
  refine le_of_tendsto hL ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (-y)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hnr : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hxy : -(n : ℝ) ≤ y := by linarith
  have h1 := h (-(n : ℝ)) y hxy
  simp only [survival] at h1
  calc μ {ω | y < X ω} * ν {ω | -(n : ℝ) < Y ω}
      ≤ μ {ω | -(n : ℝ) < X ω} * ν {ω | y < Y ω} := h1
    _ ≤ 1 * ν {ω | y < Y ω} := by gcongr; exact prob_le_one
    _ = ν {ω | y < Y ω} := one_mul _
