-- Prove2me | solution 1 for TeschlQM.Herglotz.poisson_lower_of_ball_density
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-07T21:27:41.276483+00:00
-- url     : https://prove2.me/submissions/9e5716fb-dd9c-4edf-b9ce-71b9e502f1fb

import Theorems.Thm_MeasureTheory_integral_radial_lower_of_ball_density
import Theorems.Thm_TeschlQM_Herglotz_borelTransform_im
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open MeasureTheory Filter Set
open scoped ENNReal Topology

set_option autoImplicit false

theorem solution (μ : Measure ℝ) [IsFiniteMeasure μ]
    (t δ c ε : ℝ) (hδ : 0 < δ) (hc : 0 ≤ c) (hε : 0 < ε)
    (hdensity : ∀ r : ℝ, 0 < r → r < δ →
      ENNReal.ofReal c ≤ μ (Metric.ball t r) / volume (Metric.ball t r)) :
    c * (2 / Real.pi * Real.arctan (δ / ε)) ≤
      (TeschlQM.Herglotz.borelTransform μ ((t : ℂ) + (ε : ℂ) * Complex.I)).im / Real.pi := by
  have hsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hden (r : ℝ) : 0 < ε ^ 2 + r ^ 2 := by positivity
  have hcont : Continuous (fun r : ℝ => ε / (ε ^ 2 + r ^ 2)) := by
    fun_prop (disch := intro r; exact ne_of_gt (hden r))
  have hnn : ∀ r ∈ Ici (0 : ℝ), 0 ≤ ε / (ε ^ 2 + r ^ 2) := by
    intro r _
    positivity
  have hmono : AntitoneOn (fun r : ℝ => ε / (ε ^ 2 + r ^ 2)) (Ici (0 : ℝ)) := by
    intro r hr s hs hrs
    apply div_le_div_of_nonneg_left hε.le (hden r)
    have hr0 : 0 ≤ r := hr
    have hs0 : 0 ≤ s := hs
    nlinarith
  have hbound := MeasureTheory.integral_radial_lower_of_ball_density μ t δ c hδ hc
    (fun r : ℝ => ε / (ε ^ 2 + r ^ 2)) hcont hnn hmono hdensity
  have hint : (∫ r : ℝ in 0..δ, ε / (ε ^ 2 + r ^ 2)) = Real.arctan (δ / ε) := by
    simpa using (integral_div_sq_add_sq (a := (0 : ℝ)) (b := δ) (c := ε))
  rw [hint] at hbound
  have hradial : (∫ x : ℝ, ε / (ε ^ 2 + |x - t| ^ 2) ∂μ) =
      ∫ x : ℝ, ε / ((x - t) ^ 2 + ε ^ 2) ∂μ := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by dsimp; rw [sq_abs]; ring)
  rw [hradial] at hbound
  rw [TeschlQM.Herglotz.borelTransform_im μ t ε hε]
  have h := div_le_div_of_nonneg_right hbound Real.pi_pos.le
  calc
    c * (2 / Real.pi * Real.arctan (δ / ε)) =
        (2 * c * Real.arctan (δ / ε)) / Real.pi := by ring
    _ ≤ (∫ x : ℝ, ε / ((x - t) ^ 2 + ε ^ 2) ∂μ) / Real.pi := h
