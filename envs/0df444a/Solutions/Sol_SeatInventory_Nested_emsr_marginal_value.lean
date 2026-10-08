-- Prove2me | solution 1 for SeatInventory.Nested.emsr_marginal_value
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T11:50:23.626117+00:00
-- url     : https://prove2.me/submissions/fb9c0824-60a8-41d4-9602-1a8219f76595

import Mathlib
import Definitions.Def_SeatInventory_Nested_Model

set_option autoImplicit false

open MeasureTheory in
lemma p867468ea_integrable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (r : Ω → ℕ) (hr : Measurable r) (S : ℕ) :
    Integrable (fun ω => ((min (r ω) S : ℕ) : ℝ)) μ := by
  have hm : Measurable (fun ω => ((min (r ω) S : ℕ) : ℝ)) :=
    (measurable_from_nat (f := fun n : ℕ => ((min n S : ℕ) : ℝ))).comp hr
  refine (integrable_const (S : ℝ)).mono' hm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  simp only [Real.norm_eq_abs, Nat.abs_cast]
  exact_mod_cast min_le_right _ _

open MeasureTheory SeatInventory.Nested in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (r : Ω → ℕ) (hr : Measurable r) (f : ℝ) (S : ℕ) (hS : 1 ≤ S) :
    classRevenue μ r f S - classRevenue μ r f (S - 1) = emsr μ r f S := by
  obtain ⟨k, rfl⟩ : ∃ k, S = k + 1 := ⟨S - 1, by omega⟩
  simp only [classRevenue, emsr, tailProb, Nat.add_sub_cancel]
  rw [← mul_sub, ← integral_sub (p867468ea_integrable μ r hr _) (p867468ea_integrable μ r hr _)]
  congr 1
  have hs : MeasurableSet {ω | k + 1 ≤ r ω} := hr (measurableSet_Ici (a := k + 1))
  have hfun : (fun ω => ((min (r ω) (k + 1) : ℕ) : ℝ) - ((min (r ω) k : ℕ) : ℝ))
      = Set.indicator {ω | k + 1 ≤ r ω} 1 := by
    funext ω
    by_cases h : k + 1 ≤ r ω
    · rw [Set.indicator_of_mem (by exact h)]
      rw [min_eq_right h, min_eq_right (by omega)]
      push_cast; simp
    · rw [Set.indicator_of_notMem (by exact h)]
      rw [min_eq_left (by omega), min_eq_left (by omega)]
      simp
  rw [hfun, integral_indicator_one hs]
