-- Prove2me | solution 1 for ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_band_of_largeSet_limits
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T00:06:58.672978+00:00
-- url     : https://prove2.me/submissions/b7db1ad5-7915-4a6b-8bf4-d4b1262944b0

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Theorems.Thm_ProbabilityTheory_leanlevy_chat32_integrableOn_of_bounded_of_measure_lt_top
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution (S : ConvolutionSemigroup)
    {δ ρ : ℝ} (hδ : 0 < δ) (hδρ : δ < ρ)
    (g : ℝ → ℝ) (hg_cont : Continuous g) {M : ℝ}
    (hg_bnd : ∀ x, |g x| ≤ M)
    {ν : Measure ℝ} (hν : IsLevyMeasure ν)
    {t_seq : ℕ → {t : ℝ // 0 < t}}
    (hδlim : Tendsto (fun k => (t_seq k).val⁻¹ *
        ∫ x in largeSet δ, g x ∂(S.measure (t_seq k) : Measure ℝ))
        atTop (𝓝 (∫ x in largeSet δ, g x ∂ν)))
    (hρlim : Tendsto (fun k => (t_seq k).val⁻¹ *
        ∫ x in largeSet ρ, g x ∂(S.measure (t_seq k) : Measure ℝ))
        atTop (𝓝 (∫ x in largeSet ρ, g x ∂ν))) :
    Tendsto (fun k => (t_seq k).val⁻¹ *
        ∫ x in {x | δ ≤ |x| ∧ |x| < ρ}, g x ∂(S.measure (t_seq k) : Measure ℝ))
        atTop (𝓝 (∫ x in {x | δ ≤ |x| ∧ |x| < ρ}, g x ∂ν)) := by
  have hsub : largeSet ρ ⊆ largeSet δ := by
    intro x hx
    exact le_trans (le_of_lt hδρ) hx
  have hband : {x : ℝ | δ ≤ |x| ∧ |x| < ρ} = largeSet δ \ largeSet ρ := by
    ext x
    simp [largeSet, not_le]
  have hmeasρ : MeasurableSet (largeSet ρ) :=
    (measurableSet_le measurable_const continuous_abs.measurable)
  have hsplit : ∀ (m : Measure ℝ), m (largeSet δ) < ⊤ →
      ∫ x in {x | δ ≤ |x| ∧ |x| < ρ}, g x ∂m =
      (∫ x in largeSet δ, g x ∂m) - ∫ x in largeSet ρ, g x ∂m := by
    intro m hm
    have hgi : IntegrableOn g (largeSet δ) m :=
      ProbabilityTheory.leanlevy_chat32_integrableOn_of_bounded_of_measure_lt_top
        hm hg_cont (fun x => by simpa [Real.norm_eq_abs] using hg_bnd x)
    rw [hband]
    exact setIntegral_sdiff hmeasρ hgi hsub
  have hlim := hδlim.sub hρlim
  rw [← hsplit ν (hν.measure_setOf_abs_ge_lt_top hδ)] at hlim
  refine hlim.congr (fun k => ?_)
  rw [hsplit (S.measure (t_seq k) : Measure ℝ) (measure_lt_top _ _), mul_sub]
