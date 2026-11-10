-- Prove2me | solution 1 for ProbabilityTheory.leanlevy_chat32_remainder_ball_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T23:47:21.148197+00:00
-- url     : https://prove2.me/submissions/a62e7ed0-6012-4c2a-a6c3-e9e9cf35de8e

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution {δ r : ℝ} (_hδ : 0 < δ) (hδr : δ < r) (_hr1 : r ≤ 1) (ξ : ℝ)
    (m : Measure ℝ)
    (hRint : IntegrableOn
      (fun x : ℝ => exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2)
      {x : ℝ | |x| < r} m) :
    ∫ x in {x | |x| < r},
        (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂m =
      (∫ x in {x | |x| < δ},
          (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂m) +
      ∫ x in {x | δ ≤ |x| ∧ |x| < r},
          (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂m := by
  set R : ℝ → ℂ := fun x =>
    exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2 with hR_def
  have h_inner_sub : {x : ℝ | |x| < δ} ⊆ {x : ℝ | |x| < r} := fun x hx => lt_trans hx hδr
  have h_band_sub : {x : ℝ | δ ≤ |x| ∧ |x| < r} ⊆ {x : ℝ | |x| < r} := fun x hx => hx.2
  have hR_int_ball : IntegrableOn R {x : ℝ | |x| < r} m := hRint
  have hR_int_inner : IntegrableOn R {x : ℝ | |x| < δ} m :=
    hR_int_ball.mono_set h_inner_sub
  have hR_int_band : IntegrableOn R {x : ℝ | δ ≤ |x| ∧ |x| < r} m :=
    hR_int_ball.mono_set h_band_sub
  have h_disj : Disjoint {x : ℝ | |x| < δ} {x : ℝ | δ ≤ |x| ∧ |x| < r} := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd hx'.1 (not_le.mpr hx)
  have h_union : {x : ℝ | |x| < r} = {x : ℝ | |x| < δ} ∪ {x : ℝ | δ ≤ |x| ∧ |x| < r} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_union]
    constructor
    · intro hx
      rcases lt_or_ge (|x|) δ with h | h
      · exact Or.inl h
      · exact Or.inr ⟨h, hx⟩
    · rintro (h | ⟨_, h⟩)
      · exact lt_trans h hδr
      · exact h
  have h_meas_band : MeasurableSet {x : ℝ | δ ≤ |x| ∧ |x| < r} :=
    (measurableSet_le measurable_const continuous_abs.measurable).inter
      (measurableSet_lt continuous_abs.measurable measurable_const)
  rw [h_union, setIntegral_union h_disj h_meas_band hR_int_inner hR_int_band]
