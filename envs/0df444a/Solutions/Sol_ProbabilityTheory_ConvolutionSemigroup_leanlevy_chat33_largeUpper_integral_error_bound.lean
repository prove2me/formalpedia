-- Prove2me | solution 1 for ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_largeUpper_integral_error_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T07:51:32.093376+00:00
-- url     : https://prove2.me/submissions/f0a39393-c31f-46d5-a8f3-212f534962f3

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat33_exists_largeUpperMulBCF
import Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat32_exists_annulusBCF
import Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat33_upperRamp_indicator_error_le_annulus
import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution (ρ : ℝ) (hρ : 0 < ρ) (n : ℕ)
    (g : ℝ → ℝ) (hg_cont : Continuous g) (M : ℝ) (hM : 0 ≤ M)
    (hg_bnd : ∀ x, |g x| ≤ M)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    |∫ x, min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) * g x ∂μ -
      ∫ x in largeSet ρ, g x ∂μ| ≤
      M * ∫ x, max 0 (1 - ((n + 1 : ℝ) / ρ) * max 0 (|(|x| - ρ)| - ρ / (n + 1 : ℝ))) ∂μ := by
  obtain ⟨u, hu, _⟩ :=
    ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_exists_largeUpperMulBCF
      ρ hρ n g hg_cont M hg_bnd
  obtain ⟨a, ha⟩ :=
    ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_exists_annulusBCF ρ hρ n
  have hf : Integrable (fun x => min 1 (max 0 ((|x| - ρ) * ((n + 1 : ℝ) / ρ) + 1)) * g x) μ := by
    convert u.integrable μ using 1
    funext x
    exact (hu x).symm
  have hχ : Integrable (fun x => max 0 (1 - ((n + 1 : ℝ) / ρ) * max 0 (|(|x| - ρ)| - ρ / (n + 1 : ℝ)))) μ := by
    convert a.integrable μ using 1
    funext x
    exact (ha x).symm
  have hg : Integrable g μ :=
    Integrable.mono' (integrable_const M) hg_cont.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs]
        exact hg_bnd x))
  have hmeas : MeasurableSet (largeSet ρ) :=
    (isClosed_le continuous_const continuous_abs).measurableSet
  have hind : Integrable (Set.indicator (largeSet ρ) g) μ := hg.indicator hmeas
  have heq : ∫ x in largeSet ρ, g x ∂μ =
      ∫ x, Set.indicator (largeSet ρ) g x ∂μ :=
    (integral_indicator hmeas).symm
  rw [heq, ← integral_sub hf hind]
  have hnorm := MeasureTheory.norm_integral_le_of_norm_le
    (hχ.const_mul M)
    (Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs]
      exact ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_upperRamp_indicator_error_le_annulus
        ρ hρ n g M hM hg_bnd x))
  rwa [Real.norm_eq_abs, integral_const_mul] at hnorm
