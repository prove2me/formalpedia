-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_exists_density_03e233a4d5e1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:39:04.450785+00:00
-- url     : https://prove2.me/submissions/82f70267-4ae0-4ab4-be8c-8a063741db86

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_LeOfEventuallyDown
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_le_of_eventually_up_99e470a03a01
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_le_of_eventually_down_2b051f7ea850
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_tendsto_ofReal_pow_606256ea091f
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_limsup_liminf_bounds_bfd9dae349f9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.CD
open MeasureTheory Metric Filter Topology Module
open scoped ENNReal NNReal
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable (lam nu : Measure V) [lam.IsAddHaarMeasure] [IsFiniteMeasure nu]
namespace Formalism.BasicNotions.Examples₂.CD
theorem _root_.solution
    (hq : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δ > 0, QInv nu ε δ)
    (hpos : ∀ r > 0, 0 < nu (closedBall (0 : V) r)) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      (∀ C : ℝ≥0, c < C → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, nu s ≤ C * lam s) ∧
      (∀ C : ℝ≥0, (C : ℝ≥0∞) < c → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, C * lam s ≤ nu s) := by
  have hlam0 : ∀ r : ℝ, 0 < r → lam (closedBall (0 : V) r) ≠ 0 :=
    fun r hr => (Metric.measure_closedBall_pos lam 0 hr).ne'
  have hlamT : ∀ r : ℝ, lam (closedBall (0 : V) r) ≠ ⊤ :=
    fun r => (isCompact_closedBall (0 : V) r).measure_lt_top.ne
  have hcmp : ∀ ε : ℝ, 0 < ε → ε < 1 →
      ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) * limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) ≤ ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) * liminf (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) := by
    intro ε h0 h1
    obtain ⟨δ, hδ, hqδ⟩ := hq ε h0 h1
    obtain ⟨L, -, hls, hli⟩ := limsup_liminf_bounds lam nu h0 h1 hδ hqδ
    calc ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) * limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ))
        ≤ ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) * (ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) * L) := by gcongr
      _ = ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) * (ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) * L) := by ring
      _ ≤ ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) * liminf (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) := by gcongr
  have hls_le : limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) ≤ liminf (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) := by
    have A := ENNReal.Tendsto.mul_const (tendsto_ofReal_pow (finrank ℝ V) (-1)) (Or.inl one_ne_zero) (b := limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)))
    have B := ENNReal.Tendsto.mul_const (tendsto_ofReal_pow (finrank ℝ V) 1) (Or.inl one_ne_zero) (b := liminf (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)))
    rw [one_mul] at A B
    refine le_of_tendsto_of_tendsto A B ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds zero_lt_one)] with ε h0 h1
    rw [show (1 : ℝ) + -1 * ε = 1 - ε by ring, show (1 : ℝ) + 1 * ε = 1 + ε by ring]
    exact hcmp ε h0 h1
  have heq : liminf (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) = limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) := le_antisymm Filter.liminf_le_limsup hls_le
  have hlsT : limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) < ⊤ := by
    obtain ⟨δ, hδ, hqδ⟩ := hq (1 / 2) (by norm_num) (by norm_num)
    obtain ⟨L, hL, hls, -⟩ := limsup_liminf_bounds lam nu (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num) hδ hqδ
    exact lt_of_le_of_lt hls (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL).lt_top
  have hup : ∀ C : ℝ≥0, limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) < C → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, nu s ≤ C * lam s := by
    intro C hC
    have t1 := ENNReal.Tendsto.const_mul (tendsto_ofReal_pow (finrank ℝ V) (-1)) (Or.inr (ENNReal.coe_ne_top (r := C)))
    rw [mul_one] at t1
    have hev : ∀ᶠ ε in (𝓝[>] (0 : ℝ)), (limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) < C * ENNReal.ofReal ((1 + -1 * ε) ^ finrank ℝ V)) ∧ 0 < ε ∧ ε < 1 := by
      filter_upwards [t1.eventually (lt_mem_nhds hC), self_mem_nhdsWithin,
        nhdsWithin_le_nhds (gt_mem_nhds zero_lt_one)] with ε a b c
      exact ⟨a, b, c⟩
    obtain ⟨ε, hcε, h0, h1⟩ := hev.exists
    rw [show (1 : ℝ) + -1 * ε = 1 - ε by ring] at hcε
    obtain ⟨δ, hδ, hqδ⟩ := hq ε h0 h1
    have hMe : ((C * ((1 - ε) ^ finrank ℝ V).toNNReal : ℝ≥0) : ℝ≥0∞) = C * ENNReal.ofReal ((1 - ε) ^ finrank ℝ V) := by
      rw [ENNReal.coe_mul]; rfl
    have hcM : limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) < ((C * ((1 - ε) ^ finrank ℝ V).toNNReal : ℝ≥0) : ℝ≥0∞) := by rw [hMe]; exact hcε
    have hevr := Filter.eventually_lt_of_limsup_lt hcM
    refine ⟨δ, hδ, fun s hs => le_of_eventually_up lam nu h1 hqδ _ C hMe.le ?_ s hs⟩
    filter_upwards [hevr, self_mem_nhdsWithin] with r hr hr0
    exact (ENNReal.div_le_iff_le_mul (Or.inl (hlam0 r hr0)) (Or.inl (hlamT r))).mp hr.le
  have hdown : ∀ C : ℝ≥0, (C : ℝ≥0∞) < liminf (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, C * lam s ≤ nu s := by
    intro C hC
    have t1 := ENNReal.Tendsto.const_mul (tendsto_ofReal_pow (finrank ℝ V) 1) (Or.inr (ENNReal.coe_ne_top (r := C)))
    rw [mul_one] at t1
    have hev : ∀ᶠ ε in (𝓝[>] (0 : ℝ)), (C * ENNReal.ofReal ((1 + 1 * ε) ^ finrank ℝ V) < liminf (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ))) ∧ 0 < ε ∧ ε < 1 := by
      filter_upwards [t1.eventually (gt_mem_nhds hC), self_mem_nhdsWithin,
        nhdsWithin_le_nhds (gt_mem_nhds zero_lt_one)] with ε a b c
      exact ⟨a, b, c⟩
    obtain ⟨ε, hcε, h0, h1⟩ := hev.exists
    rw [one_mul] at hcε
    obtain ⟨δ, hδ, hqδ⟩ := hq ε h0 h1
    have hMe : ((C * ((1 + ε) ^ finrank ℝ V).toNNReal : ℝ≥0) : ℝ≥0∞) = C * ENNReal.ofReal ((1 + ε) ^ finrank ℝ V) := by
      rw [ENNReal.coe_mul]; rfl
    have hcM : ((C * ((1 + ε) ^ finrank ℝ V).toNNReal : ℝ≥0) : ℝ≥0∞) < liminf (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) := by rw [hMe]; exact hcε
    have hevr := Filter.eventually_lt_of_lt_liminf hcM
    refine ⟨δ, hδ, fun s hs => le_of_eventually_down lam nu h0 hqδ _ C hMe.ge ?_ s hs⟩
    filter_upwards [hevr, self_mem_nhdsWithin] with r hr hr0
    exact (ENNReal.le_div_iff_mul_le (Or.inl (hlam0 r hr0)) (Or.inl (hlamT r))).mp hr.le
  have hc0 : limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) ≠ 0 := by
    intro hzero
    obtain ⟨δ, hδ, hqδ⟩ := hq (1 / 2) (by norm_num) (by norm_num)
    have hB : closedBall (0 : V) (δ / 2) ⊆ ball 0 δ := closedBall_subset_ball (by linarith)
    obtain ⟨C, hC0, hClt⟩ :=
      ENNReal.exists_nnreal_pos_mul_lt (hlamT (δ / 2)) (hpos (δ / 2) (by linarith)).ne'
    have hMe : ((C * ((1 - 1 / 2 : ℝ) ^ finrank ℝ V).toNNReal : ℝ≥0) : ℝ≥0∞) =
        C * ENNReal.ofReal ((1 - 1 / 2 : ℝ) ^ finrank ℝ V) := by
      rw [ENNReal.coe_mul]; rfl
    have hcM : limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)) < ((C * ((1 - 1 / 2 : ℝ) ^ finrank ℝ V).toNNReal : ℝ≥0) : ℝ≥0∞) := by
      rw [hzero, hMe]
      exact ENNReal.mul_pos (ENNReal.coe_ne_zero.mpr hC0.ne')
        (ENNReal.ofReal_pos.mpr (pow_pos (by norm_num) _)).ne'
    have hevr := Filter.eventually_lt_of_limsup_lt hcM
    have hle := le_of_eventually_up lam nu (by norm_num : (1 / 2 : ℝ) < 1) hqδ _ C hMe.le (by
      filter_upwards [hevr, self_mem_nhdsWithin] with r hr hr0
      exact (ENNReal.div_le_iff_le_mul (Or.inl (hlam0 r hr0)) (Or.inl (hlamT r))).mp hr.le) _ hB
    exact absurd hle (not_le.mpr hClt)
  refine ⟨limsup (fun r : ℝ => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r)) (𝓝[>] (0 : ℝ)), hc0, hlsT.ne, hup, fun C hC => hdown C ?_⟩
  rw [heq]
  exact hC
end Formalism.BasicNotions.Examples₂.CD
