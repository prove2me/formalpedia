-- Prove2me | solution 1 for SearchDiscovery.Reservation.appendixB_Qs_formula
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T09:09:49.947065+00:00
-- url     : https://prove2.me/submissions/5897367a-0242-4546-8e4f-27510534ae4b

import Mathlib
import Definitions.Def_SearchDiscovery_Reservation_Model

open SearchDiscovery.Reservation MeasureTheory ProbabilityTheory

theorem solution (M : SDModel) (hM : M.Standing) (x z : ℝ) :
    M.Qs x z = (∫ y in Set.Ioi (z - x), (x + y - z) ∂M.κ x) - M.cs ∧
    M.Qs x z = (∫ y in Set.Ioi (z - x), (1 - cdf (M.κ x) y)) - M.cs := by
  set μ := M.κ x with hμ
  set a := z - x with ha
  have hint : Integrable (fun y : ℝ => y) μ :=
    (hM.memLp_κ x).integrable (by norm_num)
  have hg : Integrable (fun y : ℝ => max 0 (x + y - z)) μ := by
    have h1 : Integrable (fun y : ℝ => x + y - z) μ :=
      ((integrable_const x).add hint).sub (integrable_const z)
    exact (integrable_const (0:ℝ)).sup h1
  have hQ : M.Qs x z = (∫ y, max 0 (x + y - z) ∂μ) - M.cs := rfl
  have h1 : ∫ y, max 0 (x + y - z) ∂μ = ∫ y in Set.Ioi a, (x + y - z) ∂μ := by
    rw [← integral_indicator measurableSet_Ioi]
    congr 1; funext y
    by_cases hy : y ∈ Set.Ioi a
    · rw [Set.indicator_of_mem hy]
      simp only [Set.mem_Ioi, ha] at hy
      exact max_eq_right (by linarith)
    · rw [Set.indicator_of_notMem hy]
      simp only [Set.mem_Ioi, ha, not_lt] at hy
      exact max_eq_left (by linarith)
  refine ⟨by rw [hQ, h1], ?_⟩
  rw [hQ]
  congr 1
  rw [hg.integral_eq_integral_meas_lt (Filter.Eventually.of_forall fun y => le_max_left _ _)]
  have h2 : ∫ t in Set.Ioi (0:ℝ), μ.real {y | t < max 0 (x + y - z)} =
      ∫ t in Set.Ioi (0:ℝ), (1 - cdf μ (t + a)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    simp only [Set.mem_Ioi] at ht
    have hset : {y | t < max 0 (x + y - z)} = (Set.Iic (t + a))ᶜ := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_Iic, not_le, ha, lt_max_iff]
      constructor
      · rintro (h | h) <;> linarith
      · intro h; right; linarith
    rw [hset, measureReal_compl measurableSet_Iic, cdf_eq_real]
    simp
  rw [h2]
  have h3 := integral_add_right_eq_self (μ := (volume : Measure ℝ))
    (Set.indicator (Set.Ioi a) (fun y => 1 - cdf μ y)) a
  rw [integral_indicator measurableSet_Ioi] at h3
  rw [← h3, ← integral_indicator measurableSet_Ioi]
  congr 1; funext t
  by_cases ht : t ∈ Set.Ioi (0:ℝ)
  · have : t + a ∈ Set.Ioi a := by simp only [Set.mem_Ioi] at ht ⊢; linarith
    rw [Set.indicator_of_mem ht, Set.indicator_of_mem this]
  · have : t + a ∉ Set.Ioi a := by simp only [Set.mem_Ioi, not_lt] at ht ⊢; linarith
    rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem this]
