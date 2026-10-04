-- Prove2me | solution 1 for SennottDP.Tauberian.integral_r
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T12:27:33.335978+00:00
-- url     : https://prove2.me/submissions/b1ef228e-ec31-412a-9de8-90a550826964

import Mathlib
import Definitions.Def_SennottDP_Tauberian_PowerSeries
import Definitions.Def_SennottDP_Tauberian_KaramataR

open scoped ENNReal NNReal Topology
open Filter

open SennottDP.Tauberian in
theorem solution :
    ∫ x in (0 : ℝ)..1, r x = ∫ x in Real.exp (-1)..1, x⁻¹ ∧
      ∫ x in Real.exp (-1)..1, x⁻¹ = 1 := by
  set a := Real.exp (-1) with ha
  have ha0 : 0 < a := Real.exp_pos _
  have ha1 : a ≤ 1 := by
    rw [ha]; exact Real.exp_le_one_iff.mpr (by norm_num)
  have e1 : Set.EqOn (fun _ : ℝ => (0 : ℝ)) r (Set.uIoo 0 a) := by
    intro x hx
    rw [Set.uIoo_of_le ha0.le] at hx
    simp only [r]
    rw [if_neg (not_le.mpr (by rw [← ha]; exact hx.2))]
  have i1 : IntervalIntegrable r MeasureTheory.volume 0 a :=
    (intervalIntegrable_const (c := (0 : ℝ))).congr_uIoo e1
  have e2 : Set.EqOn (fun x : ℝ => x⁻¹) r (Set.uIcc a 1) := by
    intro x hx
    rw [Set.uIcc_of_le ha1] at hx
    simp only [r]
    rw [if_pos (by rw [← ha]; exact hx.1)]
  have c2 : ContinuousOn (fun x : ℝ => x⁻¹) (Set.uIcc a 1) := by
    apply continuousOn_inv₀.mono
    intro x hx
    rw [Set.uIcc_of_le ha1] at hx
    exact ne_of_gt (lt_of_lt_of_le ha0 hx.1)
  have i2 : IntervalIntegrable r MeasureTheory.volume a 1 :=
    c2.intervalIntegrable.congr (e2.mono Set.uIoc_subset_uIcc)
  have p1 : ∫ x in (0:ℝ)..a, r x = 0 := by
    rw [← intervalIntegral.integral_congr_uIoo e1]; simp
  have p2 : ∫ x in a..1, r x = ∫ x in a..1, x⁻¹ :=
    (intervalIntegral.integral_congr e2).symm
  refine ⟨?_, ?_⟩
  · rw [← intervalIntegral.integral_add_adjacent_intervals i1 i2, p1, p2, zero_add]
  · rw [integral_inv_of_pos ha0 one_pos, ha, one_div, ← Real.exp_neg, neg_neg, Real.log_exp]
