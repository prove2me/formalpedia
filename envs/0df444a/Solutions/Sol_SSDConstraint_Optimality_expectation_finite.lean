-- Prove2me | solution 1 for SSDConstraint.Optimality.expectation_finite
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T01:21:00.274863+00:00
-- url     : https://prove2.me/submissions/755a1d16-f73d-45e6-8502-ed1ce0bd3a29

import Mathlib
import Definitions.Def_SSDConstraint_Optimality_Problem

set_option autoImplicit false

open MeasureTheory SSDConstraint.Optimality in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (a b : ℝ) :
    ∀ u ∈ U1 a b, ∀ X : Ω →₁[P] ℝ, Integrable (fun ω => u (X ω)) P := by
  intro u hu X
  obtain ⟨_, hmono, hb, c, hc, hlin⟩ := hu
  have hle : ∀ t, u t ≤ 0 := fun t => by
    have := hmono (le_max_left t b)
    rw [hb _ (le_max_right t b)] at this
    exact this
  have hge : ∀ t, u a - c * |a| - c * |t| ≤ u t := fun t => by
    rcases le_total t a with h | h
    · rw [hlin t h]
      have h1 : -(c * |t|) ≤ c * t := by
        have := neg_abs_le t; nlinarith [abs_nonneg t]
      have h2 : -(c * |a|) ≤ -(c * a) := by
        have := le_abs_self a; nlinarith [abs_nonneg a]
      linarith
    · have := hmono h
      nlinarith [abs_nonneg a, abs_nonneg t, mul_nonneg hc (abs_nonneg a),
        mul_nonneg hc (abs_nonneg t)]
  have hX : Integrable (fun ω => X ω) P := L1.integrable_coeFn X
  have hmeas : AEStronglyMeasurable (fun ω => u (X ω)) P :=
    (hmono.measurable.comp_aemeasurable (Lp.aestronglyMeasurable X).aemeasurable).aestronglyMeasurable
  refine Integrable.mono' ((integrable_const (|u a| + c * |a|)).add (hX.norm.const_mul c)) hmeas ?_
  refine Filter.Eventually.of_forall (fun ω => ?_)
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rw [abs_le]
  constructor
  · have := hge (X ω); have := neg_abs_le (u a); linarith
  · have := hle (X ω); nlinarith [abs_nonneg (u a), mul_nonneg hc (abs_nonneg a),
      mul_nonneg hc (abs_nonneg (X ω))]
