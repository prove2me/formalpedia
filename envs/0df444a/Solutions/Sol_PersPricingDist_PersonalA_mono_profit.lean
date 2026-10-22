-- Prove2me | solution 1 for PersPricingDist.PersonalA.mono_profit
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:52:07.557981+00:00
-- url     : https://prove2.me/submissions/20d3655a-8086-4fd0-bfef-1883ea586932

import Mathlib
import Definitions.Def_PersPricingDist_PersonalA_Setting

set_option autoImplicit false
open PersPricingDist.PersonalA

theorem solution (M : Model) (hM : M.Standing) : M.monoP = 1 / 2 := by
  obtain ⟨hs, hsv, hv1, hX⟩ := hM
  have hX1 : 1 ≤ M.X := by
    have : 1 < M.v / M.s := by rw [lt_div_iff₀ hs]; linarith
    linarith
  have hcont : Continuous (fun x : ℝ => M.uA x) := by
    unfold Model.uA
    exact (continuous_const.sub continuous_id).max continuous_const
  unfold Model.monoP
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 1)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  have e1 : ∫ x in (0:ℝ)..1, M.uA x = ∫ x in (0:ℝ)..1, (1 - x) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le zero_le_one] at hx
    simp only [Model.uA]
    exact max_eq_left (by linarith [hx.2])
  have e2 : ∫ x in (1:ℝ)..M.X, M.uA x = ∫ x in (1:ℝ)..M.X, (0:ℝ) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hX1] at hx
    simp only [Model.uA]
    exact max_eq_right (by linarith [hx.1])
  have e3 : ∫ x in (0:ℝ)..1, (1 - x) = ∫ x in (1 - 1 : ℝ)..(1 - 0), x :=
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => x) 1
  rw [e1, e2, e3]
  simp only [integral_id, intervalIntegral.integral_zero]
  norm_num
