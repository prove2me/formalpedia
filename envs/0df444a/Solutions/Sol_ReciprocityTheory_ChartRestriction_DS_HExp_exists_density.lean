-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.HExp.exists_density
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:17:29.60687+00:00
-- url     : https://prove2.me/submissions/865bdc4d-681e-4552-8b49-449ca044a6f0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_HaarExpA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_le_of_eventually_up
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_le_of_eventually_down
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_tendsto_ofReal_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_HExp_limsup_liminf_bounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.HExp
open MeasureTheory Metric Filter Topology Module
open scoped ENNReal NNReal
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
variable (lam nu : Measure V) [lam.IsAddHaarMeasure] [IsFiniteMeasure nu]
namespace ReciprocityTheory.ChartRestriction.DS.HExp
theorem _root_.solution
    (hq : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δ > 0, QInv nu ε δ)
    (hpos : ∀ r > 0, 0 < nu (closedBall (0 : V) r)) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      (∀ C : ℝ≥0, c < C → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, nu s ≤ C * lam s) ∧
      (∀ C : ℝ≥0, (C : ℝ≥0∞) < c → ∃ δ > 0, ∀ s ⊆ ball (0 : V) δ, C * lam s ≤ nu s) := by
  set f : ℝ → ℝ≥0∞ := fun r => nu (closedBall (0 : V) r) / lam (closedBall (0 : V) r) with hf
  set n := finrank ℝ V with hn
  have hl0 : ∀ r : ℝ, 0 < r → lam (closedBall (0 : V) r) ≠ 0 := fun r hr =>
    (measure_closedBall_pos lam 0 hr).ne'
  have hlt : ∀ r : ℝ, lam (closedBall (0 : V) r) ≠ ⊤ := fun r => measure_closedBall_lt_top.ne
  set b := limsup f (𝓝[>] (0 : ℝ)) with hb
  set a := liminf f (𝓝[>] (0 : ℝ)) with ha
  have hI : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε < 1 := Ioo_mem_nhdsGT one_pos
  have hbtop : b ≠ ⊤ := by
    obtain ⟨δ, hδ, hQ⟩ := hq (1 / 2) (by norm_num) (by norm_num)
    obtain ⟨L, hL, h1, -⟩ := limsup_liminf_bounds lam nu (by norm_num) (by norm_num) hδ hQ
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hL) h1
  have hba : b ≤ a := by
    have h1 : Tendsto (fun ε : ℝ => b * ENNReal.ofReal ((1 + (-1) * ε) ^ n)) (𝓝[>] 0) (𝓝 (b * 1)) :=
      ENNReal.Tendsto.const_mul (tendsto_ofReal_pow n (-1)) (Or.inl one_ne_zero)
    have h2 : Tendsto (fun ε : ℝ => ENNReal.ofReal ((1 + 1 * ε) ^ n) * a) (𝓝[>] 0) (𝓝 (1 * a)) :=
      ENNReal.Tendsto.mul_const (tendsto_ofReal_pow n 1) (Or.inl one_ne_zero)
    rw [mul_one] at h1
    rw [one_mul] at h2
    refine le_of_tendsto_of_tendsto h1 h2 ?_
    filter_upwards [hI] with ε hε
    obtain ⟨δ, hδ, hQ⟩ := hq ε hε.1 hε.2
    obtain ⟨L, hL, h3, h4⟩ := limsup_liminf_bounds lam nu hε.1 hε.2 hδ hQ
    have e1 : (1 + (-1) * ε) = 1 - ε := by ring
    have e2 : (1 + 1 * ε) = 1 + ε := by ring
    rw [e1, e2]
    calc b * ENNReal.ofReal ((1 - ε) ^ n)
        ≤ (ENNReal.ofReal ((1 + ε) ^ n) * L) * ENNReal.ofReal ((1 - ε) ^ n) := by gcongr
      _ = ENNReal.ofReal ((1 + ε) ^ n) * (ENNReal.ofReal ((1 - ε) ^ n) * L) := by ring
      _ ≤ ENNReal.ofReal ((1 + ε) ^ n) * a := by gcongr
  have hft : Tendsto f (𝓝[>] 0) (𝓝 b) := tendsto_of_le_liminf_of_limsup_le hba le_rfl
  have hup : ∀ M : ℝ≥0, b < M → ∀ᶠ r in 𝓝[>] (0 : ℝ),
      nu (closedBall (0 : V) r) ≤ M * lam (closedBall (0 : V) r) := by
    intro M hM
    filter_upwards [hft.eventually (gt_mem_nhds hM), self_mem_nhdsWithin] with r hr hr0
    exact (ENNReal.div_le_iff (hl0 r hr0) (hlt r)).mp hr.le
  have hdown : ∀ M : ℝ≥0, (M : ℝ≥0∞) < b → ∀ᶠ r in 𝓝[>] (0 : ℝ),
      M * lam (closedBall (0 : V) r) ≤ nu (closedBall (0 : V) r) := by
    intro M hM
    filter_upwards [hft.eventually (lt_mem_nhds hM), self_mem_nhdsWithin] with r hr hr0
    exact (ENNReal.le_div_iff_mul_le (Or.inl (hl0 r hr0)) (Or.inl (hlt r))).mp hr.le
  refine ⟨b, ?_, hbtop, ?_, ?_⟩
  · intro hb0
    obtain ⟨δ, hδ, hQ⟩ := hq (1 / 2) (by norm_num) (by norm_num)
    have hz : nu (ball (0 : V) δ) = 0 := by
      by_contra hne
      have hlb : lam (ball (0 : V) δ) ≠ ⊤ := measure_ball_lt_top.ne
      have hpos' : 0 < nu (ball (0 : V) δ) / lam (ball (0 : V) δ) :=
        ENNReal.div_pos hne hlb
      obtain ⟨M', hM'0, hM'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hpos'
      have hM'pos : 0 < M' := by exact_mod_cast hM'0
      have hlt' := ENNReal.mul_lt_of_lt_div hM'
      have hkpos : 0 < Real.toNNReal ((1 - 1 / 2 : ℝ) ^ n) := by
        rw [Real.toNNReal_pos]; positivity
      have := le_of_eventually_up lam nu (ε := 1 / 2) (by norm_num) hQ
        (M' * Real.toNNReal ((1 - 1 / 2 : ℝ) ^ n)) M'
        (by rw [ENNReal.coe_mul]; rfl)
        (hup _ (by rw [hb0]; exact_mod_cast mul_pos hM'pos hkpos)) (ball 0 δ) subset_rfl
      exact absurd hlt' (not_lt.mpr this)
    have h1 := hpos (δ / 2) (by linarith)
    have h2 : nu (closedBall (0 : V) (δ / 2)) ≤ nu (ball (0 : V) δ) :=
      measure_mono (closedBall_subset_ball (by linarith))
    rw [hz] at h2
    exact absurd h1 (not_lt.mpr h2)
  · intro C hC
    obtain ⟨C', hC'1, hC'2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hC
    have h1 : Tendsto (fun ε : ℝ => (C : ℝ≥0∞) * ENNReal.ofReal ((1 + (-1) * ε) ^ n)) (𝓝[>] 0)
        (𝓝 ((C : ℝ≥0∞) * 1)) :=
      ENNReal.Tendsto.const_mul (tendsto_ofReal_pow n (-1)) (Or.inl one_ne_zero)
    rw [mul_one] at h1
    obtain ⟨ε, hε, hε01⟩ := ((h1.eventually (lt_mem_nhds hC'2)).and hI).exists
    obtain ⟨δ, hδ, hQ⟩ := hq ε hε01.1 hε01.2
    have e1 : (1 + (-1) * ε) = 1 - ε := by ring
    rw [e1] at hε
    exact ⟨δ, hδ, fun s hs => le_of_eventually_up lam nu hε01.2 hQ C' C hε.le (hup C' hC'1) s hs⟩
  · intro C hC
    obtain ⟨C', hC'1, hC'2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hC
    have h1 : Tendsto (fun ε : ℝ => (C : ℝ≥0∞) * ENNReal.ofReal ((1 + 1 * ε) ^ n)) (𝓝[>] 0)
        (𝓝 ((C : ℝ≥0∞) * 1)) :=
      ENNReal.Tendsto.const_mul (tendsto_ofReal_pow n 1) (Or.inl one_ne_zero)
    rw [mul_one] at h1
    obtain ⟨ε, hε, hε01⟩ := ((h1.eventually (gt_mem_nhds hC'1)).and hI).exists
    obtain ⟨δ, hδ, hQ⟩ := hq ε hε01.1 hε01.2
    have e1 : (1 + 1 * ε) = 1 + ε := by ring
    rw [e1] at hε
    exact ⟨δ, hδ, fun s hs => le_of_eventually_down lam nu hε01.1 hQ C' C hε.le (hdown C' hC'2) s hs⟩
end ReciprocityTheory.ChartRestriction.DS.HExp
