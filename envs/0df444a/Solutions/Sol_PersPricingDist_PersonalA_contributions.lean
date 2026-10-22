-- Prove2me | solution 1 for PersPricingDist.PersonalA.contributions
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:16:51.337631+00:00
-- url     : https://prove2.me/submissions/daa030dd-67e5-4aa2-8037-f3074b638b00

import Mathlib
import Definitions.Def_PersPricingDist_PersonalA_Setting
set_option autoImplicit false
open PersPricingDist.PersonalA

theorem EF_lin (a b c d : ℝ) :
    ∫ x in c..d, (a - b * x) = a * (d - c) - b * (d ^ 2 - c ^ 2) / 2 := by
  rw [intervalIntegral.integral_sub (by simp) (by apply Continuous.intervalIntegrable; fun_prop)]
  rw [intervalIntegral.integral_const_mul]
  simp [integral_id]
  ring

theorem solution (M : Model) (hM : M.Standing) :
    M.alpha = (1 - M.v) ^ 2 / (2 * (1 - M.s)) ∧
    M.beta = (M.v - M.s) ^ 2 / (2 * M.s * (1 - M.s)) := by
  obtain ⟨hs, hsv, hv1, hX⟩ := hM
  have h1s : 0 < 1 - M.s := by linarith
  have hxh0 : 0 ≤ M.xhat := by unfold Model.xhat; apply div_nonneg <;> linarith
  have hxh1 : M.xhat ≤ 1 := by
    unfold Model.xhat; rw [div_le_one h1s]; linarith
  have hxhv : M.xhat ≤ M.v / M.s := by
    unfold Model.xhat; rw [div_le_div_iff₀ h1s hs]; nlinarith
  have hxhm : (1 - M.s) * M.xhat = 1 - M.v := by unfold Model.xhat; field_simp
  have h1v : 1 ≤ M.v / M.s := by rw [le_div_iff₀ hs]; linarith
  have hvs : M.v / M.s ≤ M.X := hX
  constructor
  · unfold Model.alpha
    have : ∫ x in (0 : ℝ)..M.xhat, (M.uA x - M.uB x) = ∫ x in (0 : ℝ)..M.xhat, ((1 - M.v) - (1 - M.s) * x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hxh0] at hx
      obtain ⟨hx0, hx1⟩ := hx
      have e1 : M.uA x = 1 - x := by unfold Model.uA; exact max_eq_left (by linarith)
      have e2 : M.uB x = M.v - M.s * x := by
        unfold Model.uB; apply max_eq_left
        have : x ≤ M.v / M.s := le_trans hx1 hxhv
        rw [le_div_iff₀ hs] at this; linarith
      simp only [e1, e2]; ring
    rw [this, EF_lin]
    unfold Model.xhat
    field_simp
    ring
  · unfold Model.beta
    have hcont : Continuous (fun x : ℝ => M.uB x - M.uA x) := by
      unfold Model.uA Model.uB; fun_prop
    have hI : ∀ a b : ℝ, IntervalIntegrable (fun x : ℝ => M.uB x - M.uA x) MeasureTheory.volume a b :=
      fun a b => hcont.intervalIntegrable a b
    rw [← intervalIntegral.integral_add_adjacent_intervals (hI _ 1) (hI 1 _),
      ← intervalIntegral.integral_add_adjacent_intervals (hI 1 (M.v / M.s)) (hI (M.v / M.s) _)]
    have i1 : ∫ x in M.xhat..1, (M.uB x - M.uA x) = ∫ x in M.xhat..1, (-(1 - M.v) - (-(1 - M.s)) * x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le hxh1] at hx
      obtain ⟨hx0, hx1⟩ := hx
      have e1 : M.uA x = 1 - x := by unfold Model.uA; exact max_eq_left (by linarith)
      have e2 : M.uB x = M.v - M.s * x := by
        unfold Model.uB; apply max_eq_left
        have : x ≤ M.v / M.s := le_trans hx1 h1v
        rw [le_div_iff₀ hs] at this; linarith
      simp only [e1, e2]; ring
    have i2 : ∫ x in (1:ℝ)..(M.v / M.s), (M.uB x - M.uA x) = ∫ x in (1:ℝ)..(M.v / M.s), (M.v - M.s * x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le h1v] at hx
      obtain ⟨hx0, hx1⟩ := hx
      have e1 : M.uA x = 0 := by unfold Model.uA; exact max_eq_right (by linarith)
      have e2 : M.uB x = M.v - M.s * x := by
        unfold Model.uB; apply max_eq_left
        rw [le_div_iff₀ hs] at hx1; linarith
      simp only [e1, e2]; ring
    have i3 : ∫ x in (M.v / M.s)..M.X, (M.uB x - M.uA x) = 0 := by
      have : ∫ x in (M.v / M.s)..M.X, (M.uB x - M.uA x) = ∫ x in (M.v / M.s)..M.X, (0:ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        rw [Set.uIcc_of_le hvs] at hx
        obtain ⟨hx0, hx1⟩ := hx
        have e1 : M.uA x = 0 := by unfold Model.uA; exact max_eq_right (by linarith)
        have e2 : M.uB x = 0 := by
          unfold Model.uB; apply max_eq_right
          rw [div_le_iff₀ hs] at hx0; linarith
        simp only [e1, e2]; ring
      rw [this]; simp
    rw [i1, i2, i3, EF_lin, EF_lin]
    unfold Model.xhat
    field_simp
    ring
