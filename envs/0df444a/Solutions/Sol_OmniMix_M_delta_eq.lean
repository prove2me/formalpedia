-- Prove2me | solution 1 for OmniMix.M_delta_eq
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:20:06.448462+00:00
-- url     : https://prove2.me/submissions/6370884e-5240-443e-812e-1dae62d0bde8

import Mathlib
import Definitions.Def_OmniMix_Idelta
import Definitions.Def_OmniMix_deltaT

open OmniMix in
theorem solution (T : ℕ) :
    ∫ v in Idelta (deltaT T), 1 / (v * (1 - v)) = 2 * Real.log (2 * (T : ℝ) + 1) := by
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = deltaT T := ⟨_, rfl⟩
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  have hδpos : 0 < δ := by rw [hδ]; unfold deltaT; positivity
  have h1 : 1 - δ = (2 * (T : ℝ) + 1) * δ := by
    rw [hδ]; unfold deltaT; field_simp <;> ring
  have hle : δ ≤ 1 - δ := by rw [h1]; nlinarith
  rw [← hδ]
  unfold Idelta
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hle]
  have hmem : ∀ x ∈ Set.uIcc δ (1 - δ), 0 < x ∧ 0 < 1 - x := by
    intro x hx
    rw [Set.uIcc_of_le hle] at hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hderiv : ∀ x ∈ Set.uIcc δ (1 - δ),
      HasDerivAt (fun v => Real.log v - Real.log (1 - v)) (1 / (x * (1 - x))) x := by
    intro x hx
    obtain ⟨hx0, hx1⟩ := hmem x hx
    have hA := Real.hasDerivAt_log hx0.ne'
    have hB : HasDerivAt (fun v => Real.log (1 - v)) ((1 - x)⁻¹ * (-1)) x :=
      (Real.hasDerivAt_log hx1.ne').comp x ((hasDerivAt_id x).const_sub 1)
    refine (hA.sub hB).congr_deriv ?_
    field_simp <;> ring
  have hint : IntervalIntegrable (fun v : ℝ => 1 / (v * (1 - v))) MeasureTheory.volume δ (1 - δ) := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
    intro x hx
    obtain ⟨hx0, hx1⟩ := hmem x hx
    exact (mul_pos hx0 hx1).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  show Real.log (1 - δ) - Real.log (1 - (1 - δ)) - (Real.log δ - Real.log (1 - δ)) = _
  rw [sub_sub_cancel, h1, Real.log_mul (by positivity) hδpos.ne']
  ring
