-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ZeroLocusDimH_root_lipschitz_core_cb1a9d56aba3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T05:25:35.19157+00:00
-- url     : https://prove2.me/submissions/a1ecc090-f0ef-48da-ad2f-bbf386a3b2ee

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ZeroLocusDimHGeo

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
open Metric Filter Topology Finset
noncomputable section
open GroundTheory.Heights₂.Heights.ZeroLocusDimH
namespace GroundTheory.Heights₂.Heights.ZeroLocusDimH
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] (N : ℕ) (c : ℕ → E → ℂ) (y₀ : E)
    (t₀ : ℂ) (hcont : ∀ k, Continuous (c k))
    (hlip : ∀ k, ∃ L : NNReal, ∃ T ∈ 𝓝 y₀, LipschitzOnWith L (c k) T)
    (hder : ∑ k ∈ range N, c k y₀ * ((k : ℂ) * t₀ ^ (k - 1)) ≠ 0) :
    ∃ δ > 0, ∃ K : ℝ, 0 ≤ K ∧ ∀ y y' : E, ∀ t t' : ℂ,
      dist y y₀ < δ → dist y' y₀ < δ → dist t t₀ < δ → dist t' t₀ < δ →
      ∑ k ∈ range N, c k y * t ^ k = 0 → ∑ k ∈ range N, c k y' * t' ^ k = 0 →
      ‖t - t'‖ ≤ K * ‖y - y'‖ := by
  set D : E × ℂ × ℂ → ℂ := fun z =>
    ∑ k ∈ range N, c k z.1 * ∑ j ∈ range k, z.2.1 ^ j * z.2.2 ^ (k - 1 - j) with hDdef
  have hDc : Continuous D := by
    refine continuous_finsetSum _ fun k _ => ((hcont k).comp continuous_fst).mul ?_
    exact continuous_finsetSum _ fun j _ => by fun_prop
  set D0 := ∑ k ∈ range N, c k y₀ * ((k : ℂ) * t₀ ^ (k - 1)) with hD0def
  have hDz : D (y₀, t₀, t₀) = D0 := by
    simp only [hDdef, hD0def]
    refine Finset.sum_congr rfl fun k _ => ?_
    congr 1
    rw [Finset.sum_congr rfl (g := fun _ => t₀ ^ (k - 1)), Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    intro j hj
    rw [← pow_add]
    congr 1
    have := Finset.mem_range.1 hj
    omega
  have hpos : 0 < ‖D0‖ / 2 := by positivity
  obtain ⟨δ2, hδ2, hD⟩ := Metric.continuous_iff.1 hDc (y₀, t₀, t₀) _ hpos
  choose L T hT hLT using hlip
  have hS : (⋂ k ∈ range N, T k) ∈ 𝓝 y₀ := (Filter.biInter_finset_mem _).2 fun k _ => hT k
  obtain ⟨δ1, hδ1, hball⟩ := Metric.mem_nhds_iff.1 hS
  refine ⟨min (min δ1 δ2) 1, by positivity, (∑ k ∈ range N, (L k : ℝ) * (‖t₀‖ + 1) ^ k) / (‖D0‖ / 2),
    by positivity, ?_⟩
  intro y y' t t' hy hy' ht ht' h1 h2
  have hyS : ∀ k ∈ range N, y ∈ T k := by
    have := hball (Metric.mem_ball.2 (lt_of_lt_of_le hy ((min_le_left _ _).trans (min_le_left _ _))))
    simpa using this
  have hyS' : ∀ k ∈ range N, y' ∈ T k := by
    have := hball (Metric.mem_ball.2 (lt_of_lt_of_le hy' ((min_le_left _ _).trans (min_le_left _ _))))
    simpa using this
  have hz : dist (y, t, t') (y₀, t₀, t₀) < δ2 := by
    have e2 : min (min δ1 δ2) 1 ≤ δ2 := (min_le_left _ _).trans (min_le_right _ _)
    rw [Prod.dist_eq, Prod.dist_eq]
    exact max_lt (hy.trans_le e2) (max_lt (ht.trans_le e2) (ht'.trans_le e2))
  have hDlow : ‖D0‖ / 2 ≤ ‖D (y, t, t')‖ := by
    have := hD _ hz
    rw [hDz, dist_eq_norm] at this
    have h3 := norm_sub_norm_le D0 (D (y, t, t'))
    rw [norm_sub_rev] at h3
    linarith
  have ht'b : ‖t'‖ ≤ ‖t₀‖ + 1 := by
    have : dist t' t₀ < 1 := ht'.trans_le (min_le_right _ _)
    rw [dist_eq_norm] at this
    have := norm_le_norm_add_norm_sub' t' t₀
    linarith
  have key : (t - t') * D (y, t, t') = ∑ k ∈ range N, (c k y' - c k y) * t' ^ k := by
    have e1 : (t - t') * D (y, t, t') = ∑ k ∈ range N, c k y * (t ^ k - t' ^ k) := by
      show (t - t') * ∑ k ∈ range N, c k y * ∑ j ∈ range k, t ^ j * t' ^ (k - 1 - j) = _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← geom_sum₂_mul t t' k]
      ring
    rw [e1]
    have : ∑ k ∈ range N, c k y * (t ^ k - t' ^ k) + ∑ k ∈ range N, (c k y - c k y') * t' ^ k =
        ∑ k ∈ range N, c k y * t ^ k - ∑ k ∈ range N, c k y' * t' ^ k := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [h1, h2, sub_zero] at this
    have e3 : ∑ k ∈ range N, (c k y' - c k y) * t' ^ k = -∑ k ∈ range N, (c k y - c k y') * t' ^ k := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [e3]
    linear_combination this
  have hbound : ‖t - t'‖ * ‖D (y, t, t')‖ ≤
      (∑ k ∈ range N, (L k : ℝ) * (‖t₀‖ + 1) ^ k) * ‖y - y'‖ := by
    rw [← norm_mul, key, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    rw [norm_mul, norm_pow]
    have hl := (hLT k).dist_le_mul y' (hyS' k hk) y (hyS k hk)
    rw [dist_eq_norm, dist_eq_norm, ← norm_neg (y' - y), neg_sub] at hl
    have hp : ‖t'‖ ^ k ≤ (‖t₀‖ + 1) ^ k := pow_le_pow_left₀ (norm_nonneg _) ht'b k
    calc ‖c k y' - c k y‖ * ‖t'‖ ^ k ≤ ((L k : ℝ) * ‖y - y'‖) * (‖t₀‖ + 1) ^ k :=
          mul_le_mul hl hp (by positivity) (by positivity)
      _ = (L k : ℝ) * (‖t₀‖ + 1) ^ k * ‖y - y'‖ := by ring
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  calc ‖t - t'‖ * (‖D0‖ / 2) ≤ ‖t - t'‖ * ‖D (y, t, t')‖ :=
        mul_le_mul_of_nonneg_left hDlow (norm_nonneg _)
    _ ≤ _ := hbound
end GroundTheory.Heights₂.Heights.ZeroLocusDimH
