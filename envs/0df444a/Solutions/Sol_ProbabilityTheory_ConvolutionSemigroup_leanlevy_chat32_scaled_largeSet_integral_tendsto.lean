-- Prove2me | solution 1 for ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_scaled_largeSet_integral_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T07:57:58.627776+00:00
-- url     : https://prove2.me/submissions/276226c6-9e5a-447a-94d3-e39f14853c74

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat33_largeUpper_integral_dct
import Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat33_largeAnnulus_integral_tendsto_zero
import Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat33_largeUpper_integral_error_bound
import Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat33_epsilon_three_sandwich
import Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat32_upperRamp_vanish_near_zero
import Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat33_annulusRamp_vanish_near_zero
import Mathlib.Topology.ContinuousMap.Bounded.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real

theorem solution (S : ConvolutionSemigroup)
    {ρ : ℝ} (hρ : 0 < ρ)
    (g : ℝ → ℝ) (hg_cont : Continuous g) {M : ℝ} (hM_nn : 0 ≤ M)
    (hg_bnd : ∀ x, |g x| ≤ M)
    {ν : Measure ℝ} (hν : IsLevyMeasure ν) (hν_atom : ν {x | |x| = ρ} = 0)
    {t_seq : ℕ → {t : ℝ // 0 < t}}
    (h_jump : ∀ (f : BoundedContinuousFunction ℝ ℝ),
        (∃ r > 0, ∀ x, |x| < r → f x = 0) →
        Tendsto (fun k => (t_seq k).val⁻¹ * ∫ x, f x ∂(S.measure (t_seq k) : Measure ℝ))
          atTop (𝓝 (∫ x, f x ∂ν))) :
    Tendsto (fun k => (t_seq k).val⁻¹ *
        ∫ x in largeSet ρ, g x ∂(S.measure (t_seq k) : Measure ℝ))
      atTop (𝓝 (∫ x in largeSet ρ, g x ∂ν)) := by
  obtain ⟨φ, hφ, hφ_lim⟩ :=
    ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_largeUpper_integral_dct
      ρ hρ g hg_cont M hg_bnd hν
  obtain ⟨χ, hχ, hχ_lim⟩ :=
    ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_largeAnnulus_integral_tendsto_zero
      ρ hρ hν hν_atom
  have hA : Tendsto (fun n : ℕ => ∫ x, φ (n + 2) x ∂ν) atTop
      (𝓝 (∫ x in largeSet ρ, g x ∂ν)) :=
    (tendsto_add_atTop_iff_nat 2).mpr hφ_lim
  have hB : Tendsto (fun n : ℕ => ∫ x, χ (n + 1) x ∂ν) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mpr hχ_lim
  have hA_time : ∀ n : ℕ, Tendsto
      (fun k => (t_seq k).val⁻¹ *
        ∫ x, φ (n + 2) x ∂(S.measure (t_seq k) : Measure ℝ))
      atTop (𝓝 (∫ x, φ (n + 2) x ∂ν)) := by
    intro n
    apply h_jump
    obtain ⟨r, hr, hzero⟩ :=
      ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat32_upperRamp_vanish_near_zero
        ρ hρ (n + 2) (by omega)
    refine ⟨r, hr, fun x hx => ?_⟩
    rw [hφ (n + 2) x, hzero x hx, zero_mul]
  have hB_time : ∀ n : ℕ, Tendsto
      (fun k => (t_seq k).val⁻¹ *
        ∫ x, χ (n + 1) x ∂(S.measure (t_seq k) : Measure ℝ))
      atTop (𝓝 (∫ x, χ (n + 1) x ∂ν)) := by
    intro n
    apply h_jump
    obtain ⟨r, hr, hzero⟩ :=
      ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_annulusRamp_vanish_near_zero
        ρ hρ (n + 2) (by omega)
    refine ⟨r, hr, fun x hx => ?_⟩
    rw [hχ (n + 1) x]
    convert hzero x hx using 1 <;> push_cast <;> ring
  have herr : ∀ n k : ℕ,
      |(t_seq k).val⁻¹ *
        ∫ x in largeSet ρ, g x ∂(S.measure (t_seq k) : Measure ℝ) -
        (t_seq k).val⁻¹ * ∫ x, φ (n + 2) x ∂(S.measure (t_seq k) : Measure ℝ)| ≤
      M * ((t_seq k).val⁻¹ *
        ∫ x, χ (n + 1) x ∂(S.measure (t_seq k) : Measure ℝ)) := by
    intro n k
    let μk : Measure ℝ := (S.measure (t_seq k) : Measure ℝ)
    have hφint : ∫ x, φ (n + 2) x ∂μk =
        ∫ x, min 1 (max 0 ((|x| - ρ) * (((n + 2 : ℕ) + 1 : ℝ) / ρ) + 1)) *
          g x ∂μk := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => hφ (n + 2) x)
    have hχint : ∫ x, χ (n + 1) x ∂μk =
        ∫ x, max 0 (1 - (((n + 2 : ℕ) + 1 : ℝ) / ρ) *
          max 0 (|(|x| - ρ)| - ρ / ((n + 2 : ℕ) + 1 : ℝ))) ∂μk := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        rw [hχ (n + 1) x]
        push_cast
        ring)
    have hbound :=
      ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_largeUpper_integral_error_bound
        ρ hρ (n + 2) g hg_cont M hM_nn hg_bnd μk
    rw [← hφint, ← hχint] at hbound
    have htinv : 0 ≤ (t_seq k).val⁻¹ :=
      inv_nonneg.mpr (le_of_lt (t_seq k).prop)
    have hscaled := mul_le_mul_of_nonneg_left hbound htinv
    change
      (t_seq k).val⁻¹ * |∫ x, φ (n + 2) x ∂μk -
        ∫ x in largeSet ρ, g x ∂μk| ≤
      (t_seq k).val⁻¹ * (M * ∫ x, χ (n + 1) x ∂μk) at hscaled
    rw [show (t_seq k).val⁻¹ * (M * ∫ x, χ (n + 1) x ∂μk) =
      M * ((t_seq k).val⁻¹ * ∫ x, χ (n + 1) x ∂μk) from by ring] at hscaled
    change
      |(t_seq k).val⁻¹ * ∫ x in largeSet ρ, g x ∂μk -
        (t_seq k).val⁻¹ * ∫ x, φ (n + 2) x ∂μk| ≤
      M * ((t_seq k).val⁻¹ * ∫ x, χ (n + 1) x ∂μk)
    rw [← mul_sub, abs_mul, abs_of_nonneg htinv, abs_sub_comm]
    exact hscaled
  exact ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_epsilon_three_sandwich
    hM_nn hA hB hA_time hB_time herr
