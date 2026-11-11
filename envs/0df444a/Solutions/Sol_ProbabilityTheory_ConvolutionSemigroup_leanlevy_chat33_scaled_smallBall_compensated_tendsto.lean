-- Prove2me | solution 1 for ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_scaled_smallBall_compensated_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T08:55:16.164904+00:00
-- url     : https://prove2.me/submissions/d1013a78-1cf8-4b4f-9dae-ad44cc393e65

import Definitions.Def_LeanLevy_Levy_LevyKhintchineProof
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Theorems.Thm_ProbabilityTheory_ConvolutionSemigroup_leanlevy_chat33_scaled_smallBall_remainder_tendsto
import Theorems.Thm_ProbabilityTheory_leanlevy_chat32_remainder_integrableOn_ball
import Theorems.Thm_ProbabilityTheory_leanlevy_chat32_sq_integrableOn_ball
import Theorems.Thm_leanlevy_chat33_scaled_small_ball_compensated_direct_identity_8738322f
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder Real
/-- Original-source compensated small-ball limit, reduced to the cubic remainder. -/
theorem solution (S : ConvolutionSemigroup)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (ξ : ℝ)
    {ν : Measure ℝ} (hν : IsLevyMeasure ν)
    (hν_r : ν {x | |x| = r} = 0)
    {t_seq : ℕ → {t : ℝ // 0 < t}} {σ_sq_r : ℝ}
    (hσ : Tendsto (fun k => (t_seq k).val⁻¹ *
        ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq k) : Measure ℝ)) atTop (𝓝 σ_sq_r))
    (h_jump : ∀ (f : BoundedContinuousFunction ℝ ℝ),
        (∃ r > 0, ∀ x, |x| < r → f x = 0) →
        Tendsto (fun k => (t_seq k).val⁻¹ * ∫ x, f x ∂(S.measure (t_seq k) : Measure ℝ))
          atTop (𝓝 (∫ x, f x ∂ν))) :
    Tendsto (fun k => ((t_seq k).val⁻¹ : ℂ) *
        ∫ x in {x | |x| < r}, (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I)
          ∂(S.measure (t_seq k) : Measure ℝ))
      atTop (𝓝 (-(↑σ_sq_r * ↑ξ ^ 2 / 2)
          + ∫ x in {x | |x| < r},
              (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂ν)) := by
  have hσ_bdd : ∃ C : ℝ, ∀ k, (t_seq k).val⁻¹ *
      ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq k) : Measure ℝ) ≤ C := by
    obtain ⟨C, hC⟩ := bddAbove_def.mp hσ.isBoundedUnder_le.bddAbove_range
    exact ⟨C, fun k => hC _ ⟨k, rfl⟩⟩
  have hrem := ProbabilityTheory.ConvolutionSemigroup.leanlevy_chat33_scaled_smallBall_remainder_tendsto S hr hr1 ξ hν hν_r hσ_bdd h_jump
  have hquad : Tendsto (fun k => (↑ξ ^ 2 / 2 : ℂ) *
      (↑((t_seq k).val⁻¹ * ∫ x in {x | |x| < r}, x ^ 2
        ∂(S.measure (t_seq k) : Measure ℝ)) : ℂ))
      atTop (𝓝 ((↑ξ ^ 2 / 2 : ℂ) * (↑σ_sq_r : ℂ))) :=
    Tendsto.const_mul _ ((Complex.continuous_ofReal.tendsto _).comp hσ)
  have hpereq : ∀ k, ((t_seq k).val⁻¹ : ℂ) *
      ∫ x in {x | |x| < r}, (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I)
        ∂(S.measure (t_seq k) : Measure ℝ) =
      (((t_seq k).val⁻¹ : ℂ) * ∫ x in {x | |x| < r},
          (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2)
          ∂(S.measure (t_seq k) : Measure ℝ)) -
      (↑ξ ^ 2 / 2 : ℂ) * (↑((t_seq k).val⁻¹ *
          ∫ x in {x | |x| < r}, x ^ 2 ∂(S.measure (t_seq k) : Measure ℝ)) : ℂ) := leanlevy_chat33_scaled_small_ball_compensated_direct_identity_8738322f (S := S) (r := r) (hr := hr) (hr1 := hr1) (ξ := ξ) (ν := ν) (hν := hν) (hν_r := hν_r) (t_seq := t_seq) (σ_sq_r := σ_sq_r) (hσ := hσ) (h_jump := h_jump) (hσ_bdd := hσ_bdd) (hquad := hquad)
  have hlim := (hrem.sub hquad).congr (fun k => (hpereq k).symm)
  have hRHS : (∫ x in {x | |x| < r},
        (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂ν) -
        (↑ξ ^ 2 / 2 : ℂ) * (↑σ_sq_r : ℂ) =
      -(↑σ_sq_r * ↑ξ ^ 2 / 2)
        + ∫ x in {x | |x| < r},
            (exp ((↑x : ℂ) * ↑ξ * I) - 1 - (↑x : ℂ) * ↑ξ * I + ((↑x : ℂ) * ↑ξ) ^ 2 / 2) ∂ν := by
    ring
  rw [← hRHS]
  exact hlim
