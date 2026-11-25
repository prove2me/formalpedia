-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.PackingSeparation.pack
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:00:03.86948+00:00
-- url     : https://prove2.me/submissions/bd915414-f535-454b-a9c4-2e670b41b1cc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralTraceNormBounds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PackingSeparation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.PackingSeparation
open NumberField InfinitePlace Module MeasureTheory Metric TraceIntegralBasis IntegralTraceNormBounds
open scoped Classical
namespace ReciprocityTheory.ChartRestriction.G.FD.PackingSeparation
theorem _root_.solution {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [MeasurableSpace W]
    [BorelSpace W] [FiniteDimensional ℝ W] [Nontrivial W] (μ : Measure W) [μ.IsAddHaarMeasure]
    (S : Finset W) (R : ℝ) (hR : 0 ≤ R) (hS : ∀ p ∈ S, ‖p‖ ≤ R)
    (hsep : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → 1 ≤ ‖p - q‖) :
    (S.card : ℝ) ≤ (1 + 2 * R) ^ finrank ℝ W := by
  set d := finrank ℝ W
  have hdisj : (S : Set W).PairwiseDisjoint fun p => ball p (1 / 2) := by
    intro p hp q hq hpq
    rw [Function.onFun, Set.disjoint_left]
    intro z hzp hzq
    rw [mem_ball, dist_eq_norm] at hzp hzq
    have h1 := hsep p hp q hq hpq
    have h2 : ‖p - q‖ ≤ ‖z - p‖ + ‖z - q‖ := by
      calc ‖p - q‖ = ‖(z - q) - (z - p)‖ := by congr 1; abel
        _ ≤ ‖z - q‖ + ‖z - p‖ := norm_sub_le _ _
        _ = ‖z - p‖ + ‖z - q‖ := add_comm _ _
    linarith
  have hsub : (⋃ p ∈ S, ball p (1 / 2)) ⊆ ball (0 : W) (R + 1 / 2) := by
    intro z hz
    simp only [Set.mem_iUnion, mem_ball, dist_eq_norm] at hz
    obtain ⟨p, hp, hzp⟩ := hz
    rw [mem_ball, dist_eq_norm, sub_zero]
    calc ‖z‖ = ‖(z - p) + p‖ := by rw [sub_add_cancel]
      _ ≤ ‖z - p‖ + ‖p‖ := norm_add_le _ _
      _ < 1 / 2 + R := by linarith [hS p hp]
      _ = R + 1 / 2 := add_comm _ _
  have h := measure_mono (μ := μ) hsub
  rw [measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)] at h
  simp only [Measure.addHaar_ball μ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
    Measure.addHaar_ball μ _ (by positivity : (0 : ℝ) ≤ R + 1 / 2), Finset.sum_const,
    nsmul_eq_mul] at h
  rw [← mul_assoc] at h
  have hc0 : μ (ball 0 1) ≠ 0 := (measure_ball_pos μ 0 one_pos).ne'
  have hctop : μ (ball 0 1) ≠ ⊤ := measure_ball_lt_top.ne
  have h2 := (ENNReal.mul_le_mul_iff_left hc0 hctop).mp h
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
  have h3 : (S.card : ℝ) = (S.card : ℝ) * (1 / 2) ^ d * 2 ^ d := by
    rw [mul_assoc, ← mul_pow]
    norm_num
  rw [h3]
  calc (S.card : ℝ) * (1 / 2) ^ d * 2 ^ d ≤ (R + 1 / 2) ^ d * 2 ^ d :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = (1 + 2 * R) ^ d := by
        rw [← mul_pow]
        congr 1
        ring
end ReciprocityTheory.ChartRestriction.G.FD.PackingSeparation
