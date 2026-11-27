-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.four_sign
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:30:25.115025+00:00
-- url     : https://prove2.me/submissions/109ed1a7-6f90-4461-a4d8-311b0feab108

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FourBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (f : ℕ) (hI : FOURIndepStatement f) (hB : FOURBoundStatement f) :
    FOURSignStatement f := by
  intro Ω h b0 κ C E hΩ hpre hd hper hray hgrowth ν hne
  by_contra hneg0
  have hneg := not_le.mp hneg0
  obtain ⟨S0, hS0⟩ : ∃ S : ℝ, S = ∑ k, (ν k : ℝ) * b0 k := ⟨_, rfl⟩
  obtain ⟨Sκ, hSκ⟩ : ∃ S : ℝ, S = ∑ k, (ν k : ℝ) * κ k := ⟨_, rfl⟩
  rw [← hSκ] at hneg
  have hb0 : b0 ∈ Ω := by simpa using hray 0 le_rfl
  have hsum : ∀ t : ℝ, ∑ k, (ν k : ℝ) * (b0 + t • κ) k = S0 + t * Sκ := by
    intro t
    rw [hS0, hSκ, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, β = -2 * Real.pi * Sκ := ⟨_, rfl⟩
  have hβpos : 0 < β := by
    rw [hβ]; nlinarith [mul_pos Real.pi_pos (neg_pos.mpr hneg)]
  have hK : 0 < ‖fourCoeff h b0 ν‖ * Real.exp (-2 * Real.pi * S0) :=
    mul_pos (norm_pos_iff.mpr hne) (Real.exp_pos _)
  have hle : ∀ t : ℝ, 0 ≤ t → ‖fourCoeff h b0 ν‖ * Real.exp (-2 * Real.pi * S0) ≤
      C * ((1 + t) ^ E * Real.exp (-β * t)) := by
    intro t ht
    have hcoef := hI Ω h hΩ hpre hd hper b0 hb0 (b0 + t • κ) (hray t ht) ν
    have hbd := hB h (b0 + t • κ) ν (C * (1 + t) ^ E) (hgrowth t ht)
    rw [← hcoef, hsum t] at hbd
    have hexp : Real.exp (-2 * Real.pi * (S0 + t * Sκ)) =
        Real.exp (-2 * Real.pi * S0) * Real.exp (β * t) := by
      rw [← Real.exp_add, hβ]; congr 1; ring
    rw [hexp] at hbd
    have h1 : Real.exp (β * t) * Real.exp (-β * t) = 1 := by
      rw [← Real.exp_add, show β * t + -β * t = 0 by ring, Real.exp_zero]
    calc ‖fourCoeff h b0 ν‖ * Real.exp (-2 * Real.pi * S0)
        = ‖fourCoeff h b0 ν‖ * (Real.exp (-2 * Real.pi * S0) * Real.exp (β * t)) *
            Real.exp (-β * t) := by
          linear_combination (-(‖fourCoeff h b0 ν‖ * Real.exp (-2 * Real.pi * S0))) * h1
      _ ≤ C * (1 + t) ^ E * Real.exp (-β * t) :=
          mul_le_mul_of_nonneg_right hbd (Real.exp_pos _).le
      _ = C * ((1 + t) ^ E * Real.exp (-β * t)) := by ring
  have hlim : Tendsto (fun t : ℝ => C * ((1 + t) ^ E * Real.exp (-β * t))) atTop (𝓝 0) := by
    have h1 := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero E β hβpos
    have h2 : Tendsto (fun t : ℝ => 1 + t) atTop atTop :=
      tendsto_atTop_mono (fun t => le_add_of_nonneg_left zero_le_one) tendsto_id
    have h3 := (h1.comp h2).const_mul (Real.exp β)
    rw [mul_zero] at h3
    have h4 : Tendsto (fun t : ℝ => (1 + t) ^ E * Real.exp (-β * t)) atTop (𝓝 0) := by
      refine h3.congr fun t => ?_
      have he : Real.exp β * Real.exp (-β * (1 + t)) = Real.exp (-β * t) := by
        rw [← Real.exp_add]; congr 1; ring
      show Real.exp β * ((1 + t) ^ E * Real.exp (-β * (1 + t))) = _
      rw [← he]; ring
    have h5 := h4.const_mul C
    rwa [mul_zero] at h5
  have hfin := ge_of_tendsto hlim ((eventually_ge_atTop (0 : ℝ)).mono fun t ht => hle t ht)
  linarith
end ReciprocityTheory.L2DbarEstimates.Y
