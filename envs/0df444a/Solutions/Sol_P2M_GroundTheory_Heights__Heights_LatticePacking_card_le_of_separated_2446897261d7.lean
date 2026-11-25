-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LatticePacking_card_le_of_separated_2446897261d7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:02:19.261798+00:00
-- url     : https://prove2.me/submissions/19e0d5c6-f937-4264-98f0-b3cb76663037

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_CardLeOfSeparated

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Metric Module Function
open scoped ENNReal
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace LatticePacking
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (s : Finset E) {ρ δ : ℝ} (hδ : 0 < δ) (hρ : 0 ≤ ρ)
    (hs : ∀ c ∈ s, ‖c‖ ≤ ρ) (h : ∀ c ∈ s, ∀ d ∈ s, c ≠ d → δ ≤ ‖c - d‖) :
    (s.card : ℝ) ≤ ((2 * ρ + δ) / δ) ^ finrank ℝ E := by
  borelize E
  let μ : Measure E := Measure.addHaar
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have hR : 0 < ρ + δ / 2 := by linarith
  have D : Set.Pairwise (s : Set E) (Disjoint on fun c => ball (c : E) (δ / 2)) := by
    rintro c hc d hd hcd
    apply ball_disjoint_ball
    rw [dist_eq_norm]
    have := h c hc d hd hcd
    linarith
  have A_subset : (⋃ c ∈ s, ball (c : E) (δ / 2)) ⊆ ball (0 : E) (ρ + δ / 2) := by
    refine Set.iUnion₂_subset fun x hx => ?_
    apply ball_subset_ball'
    rw [dist_zero_right]
    linarith [hs x hx]
  have I : (s.card : ℝ≥0∞) * ENNReal.ofReal ((δ / 2) ^ finrank ℝ E) * μ (ball 0 1) ≤
      ENNReal.ofReal ((ρ + δ / 2) ^ finrank ℝ E) * μ (ball 0 1) :=
    calc
      (s.card : ℝ≥0∞) * ENNReal.ofReal ((δ / 2) ^ finrank ℝ E) * μ (ball 0 1)
          = μ (⋃ c ∈ s, ball (c : E) (δ / 2)) := by
        rw [measure_biUnion_finset D fun c _ => measurableSet_ball]
        simp only [μ.addHaar_ball_of_pos _ hδ2]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ μ (ball (0 : E) (ρ + δ / 2)) := measure_mono A_subset
      _ = ENNReal.ofReal ((ρ + δ / 2) ^ finrank ℝ E) * μ (ball 0 1) := by
        simp only [μ.addHaar_ball_of_pos _ hR]
  have J : (s.card : ℝ≥0∞) * ENNReal.ofReal ((δ / 2) ^ finrank ℝ E) ≤
      ENNReal.ofReal ((ρ + δ / 2) ^ finrank ℝ E) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos _ _ zero_lt_one).ne' measure_ball_lt_top.ne).1 I
  have K : (s.card : ℝ) * (δ / 2) ^ finrank ℝ E ≤ (ρ + δ / 2) ^ finrank ℝ E := by
    have := ENNReal.toReal_le_of_le_ofReal (pow_nonneg hR.le _) J
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hδ2.le _),
      ENNReal.toReal_natCast] at this
  have e : (2 * ρ + δ) / δ = (ρ + δ / 2) / (δ / 2) := by
    rw [div_eq_div_iff hδ.ne' hδ2.ne']; ring
  rw [e, div_pow, le_div_iff₀ (pow_pos hδ2 _)]
  exact K
end LatticePacking
end GroundTheory.Heights₂.Heights
