-- Prove2me | solution 1 for ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat31_drift_term
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T22:42:24.955999+00:00
-- url     : https://prove2.me/submissions/da1ce5b9-b73f-4851-a1cc-f72fab1698ea

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Monoid.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder

/-- The original drift limit, factored through the complexification of the real integral. -/
theorem solution
    (S : ProbabilityTheory.ConvolutionSemigroup) (ξ : ℝ) {r : ℝ}
    {t_seq : ℕ → {t : ℝ // 0 < t}}
    (_ht : Tendsto (fun n => (t_seq n).val) atTop (𝓝 0))
    {b : ℝ} (hb : Tendsto (fun n =>
      (t_seq n).val⁻¹ * ∫ x in {x | |x| < r}, x ∂(S.measure (t_seq n) : Measure ℝ))
      atTop (𝓝 b)) :
    Tendsto (fun n =>
      ((t_seq n).val⁻¹ : ℂ) *
        ∫ x in {x | |x| < r}, (↑x * ↑ξ * I) ∂(S.measure (t_seq n) : Measure ℝ))
      atTop (𝓝 (↑b * ↑ξ * I)) := by
  suffices h : Tendsto (fun n =>
      ↑((t_seq n).val⁻¹ * ∫ x in {x | |x| < r}, x ∂(S.measure (t_seq n) : Measure ℝ)) *
        ((↑ξ : ℂ) * I)) atTop (𝓝 (↑b * ↑ξ * I)) by
    refine h.congr (fun n => ?_)
    have hint : ∫ x in {x | |x| < r}, ((↑x : ℂ) * ↑ξ * I) ∂(S.measure (t_seq n) : Measure ℝ) =
        ↑(∫ x in {x | |x| < r}, x ∂(S.measure (t_seq n) : Measure ℝ)) * (↑ξ * I) := by
      simp_rw [mul_assoc]
      have hsmul : ∀ x : ℝ, (↑x : ℂ) * ((↑ξ : ℂ) * I) =
          (↑x : ℂ) • ((↑ξ : ℂ) * I) := by
        intro x
        rw [smul_eq_mul]
      simp_rw [hsmul]
      rw [integral_smul_const]
      congr 1
      exact integral_ofReal
    rw [hint]
    push_cast
    ring
  rw [show (↑b : ℂ) * ↑ξ * I = ↑b * (↑ξ * I) from by ring]
  exact Filter.Tendsto.mul_const ((↑ξ : ℂ) * I) hb.ofReal
