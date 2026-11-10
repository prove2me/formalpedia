-- Prove2me | solution 1 for ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_scaled_band_integral_tendsto
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T00:14:36.389041+00:00
-- url     : https://prove2.me/submissions/f68f4723-3f2e-4f33-8ea3-226313ea3192
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat32_scaled_largeSet_integral_tendsto
import Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat32_band_of_largeSet_limits
import Mathlib.Topology.ContinuousMap.Bounded.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution (S : ConvolutionSemigroup)
    {δ ρ : ℝ} (hδ : 0 < δ) (hδρ : δ < ρ)
    (g : ℝ → ℝ) (hg_cont : Continuous g) {M : ℝ} (hM_nn : 0 ≤ M)
    (hg_bnd : ∀ x, |g x| ≤ M)
    {ν : Measure ℝ} (hν : IsLevyMeasure ν)
    (hν_δ : ν {x | |x| = δ} = 0) (hν_ρ : ν {x | |x| = ρ} = 0)
    {t_seq : ℕ → {t : ℝ // 0 < t}}
    (h_jump : ∀ (f : BoundedContinuousFunction ℝ ℝ),
        (∃ r > 0, ∀ x, |x| < r → f x = 0) →
        Tendsto (fun k => (t_seq k).val⁻¹ * ∫ x, f x ∂(S.measure (t_seq k) : Measure ℝ))
          atTop (𝓝 (∫ x, f x ∂ν))) :
    Tendsto (fun k => (t_seq k).val⁻¹ *
        ∫ x in {x | δ ≤ |x| ∧ |x| < ρ}, g x ∂(S.measure (t_seq k) : Measure ℝ))
      atTop (𝓝 (∫ x in {x | δ ≤ |x| ∧ |x| < ρ}, g x ∂ν)) := by
  have hρ : 0 < ρ := lt_trans hδ hδρ
  have hδlim :=
    ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_scaled_largeSet_integral_tendsto
      S hδ g hg_cont hM_nn hg_bnd hν hν_δ h_jump
  have hρlim :=
    ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_scaled_largeSet_integral_tendsto
      S hρ g hg_cont hM_nn hg_bnd hν hν_ρ h_jump
  exact ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_band_of_largeSet_limits
    S hδ hδρ g hg_cont hg_bnd hν hδlim hρlim
