-- Prove2me | solution 1 for SennottDP.AvgFinite.prop_4_5_1_power_series
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:33:18.87453+00:00
-- url     : https://prove2.me/submissions/69565860-0cec-46bc-92a5-125d3bfbd420

import Mathlib
import Definitions.Def_SennottDP_AvgFinite_Criteria

open scoped ENNReal NNReal

namespace SennottDP.AvgFinite.P451

open SennottDP.AvgFinite

theorem p451_mono {S : Type*} {Act : Type*} [Countable S] {M : MDC S Act} (θ : Policy M) (i : S)
    {α β : ℝ} (h : α ≤ β) : discCost θ α i ≤ discCost θ β i := by
  unfold discCost
  refine ENNReal.tsum_le_tsum fun t => ?_
  gcongr

end SennottDP.AvgFinite.P451

open SennottDP.AvgFinite SennottDP.AvgFinite.P451 in
theorem solution {S : Type*} {Act : Type*} [Countable S] (M : MDC S Act)
    (θ : Policy M) (i : S) :
    ∃ R : ℝ≥0∞,
      (∀ α : ℝ, 0 ≤ α → ENNReal.ofReal α < R → discCost θ α i ≠ ⊤) ∧
      (∀ α : ℝ, R < ENNReal.ofReal α → discCost θ α i = ⊤) ∧
      (0 < R → ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun α : ℝ => (discCost θ α i).toReal)
        {α : ℝ | 0 < α ∧ ENNReal.ofReal α < R}) := by
  set R : ℝ≥0∞ := ⨆ (α : ℝ) (_ : 0 ≤ α ∧ discCost θ α i ≠ ⊤), ENNReal.ofReal α with hR
  -- below `R` there is a larger point of convergence
  have hbelow : ∀ α : ℝ, ENNReal.ofReal α < R →
      ∃ β : ℝ, 0 ≤ β ∧ discCost θ β i ≠ ⊤ ∧ ENNReal.ofReal α < ENNReal.ofReal β := by
    intro α hα
    obtain ⟨β, hβ⟩ := lt_iSup_iff.mp hα
    obtain ⟨hβ', hlt⟩ := lt_iSup_iff.mp hβ
    exact ⟨β, hβ'.1, hβ'.2, hlt⟩
  have h1 : ∀ α : ℝ, 0 ≤ α → ENNReal.ofReal α < R → discCost θ α i ≠ ⊤ := by
    intro α hα0 hα
    obtain ⟨β, hβ0, hβ, hlt⟩ := hbelow α hα
    have hab : α ≤ β := ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hα0).mp hlt).le
    exact ne_top_of_le_ne_top hβ (p451_mono θ i hab)
  refine ⟨R, h1, ?_, ?_⟩
  · intro α hα
    by_contra hne
    have hα0 : 0 ≤ α := by
      by_contra hneg
      rw [ENNReal.ofReal_of_nonpos (by linarith)] at hα
      exact absurd hα (not_lt.mpr bot_le)
    have : ENNReal.ofReal α ≤ R :=
      le_iSup₂ (f := fun (α : ℝ) (_ : 0 ≤ α ∧ discCost θ α i ≠ ⊤) => ENNReal.ofReal α) α ⟨hα0, hne⟩
    exact absurd hα (not_lt.mpr this)
  · intro hRpos
    set u : ℕ → ℝ≥0∞ := fun t => expCost θ i t with hu
    set c : ℕ → ℝ := fun t => (u t).toReal with hc
    set p : FormalMultilinearSeries ℝ ℝ ℝ := FormalMultilinearSeries.ofScalars ℝ c with hp
    set D : Set ℝ := {α : ℝ | 0 < α ∧ ENNReal.ofReal α < R} with hD
    -- at a positive point of convergence every coefficient is finite
    have hfinite : ∀ β : ℝ, 0 < β → discCost θ β i ≠ ⊤ → ∀ t, u t ≠ ⊤ := by
      intro β hβ hfin t hut
      apply hfin
      unfold discCost
      refine ENNReal.tsum_eq_top_of_eq_top ⟨t, ?_⟩
      rw [show expCost θ i t = ⊤ from hut]
      exact ENNReal.mul_top (pow_ne_zero _ (ENNReal.ofReal_pos.mpr hβ).ne')
    -- the real value of the series
    have hval : ∀ β : ℝ, 0 < β → discCost θ β i ≠ ⊤ →
        (discCost θ β i).toReal = ∑' t, c t * β ^ t ∧ Summable (fun t => c t * β ^ t) := by
      intro β hβ hfin
      have hu' := hfinite β hβ hfin
      have hterm : ∀ t, ENNReal.ofReal β ^ t * u t ≠ ⊤ := fun t =>
        ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (hu' t)
      have hconv : ∀ t, (ENNReal.ofReal β ^ t * u t).toReal = c t * β ^ t := by
        intro t
        rw [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hβ.le, mul_comm]
      constructor
      · unfold discCost
        rw [ENNReal.tsum_toReal_eq hterm]
        exact tsum_congr hconv
      · have := ENNReal.summable_toReal (f := fun t => ENNReal.ofReal β ^ t * u t) hfin
        simpa [hconv] using this
    -- every point of `D` lies inside the radius of convergence
    have hrad : ∀ α ∈ D, ENNReal.ofReal α < p.radius := by
      intro α hα
      obtain ⟨β, hβ0, hβ, hlt⟩ := hbelow α hα.2
      have hβpos : 0 < β := by
        have := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hα.1.le).mp hlt
        linarith [hα.1]
      have hsum := (hval β hβpos hβ).2
      have hle : ((β.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ p.radius := by
        refine p.le_radius_of_summable ?_
        have e : ∀ n, ‖p n‖ * ((β.toNNReal : ℝ≥0) : ℝ) ^ n = c n * β ^ n := by
          intro n
          rw [hp, FormalMultilinearSeries.ofScalars_norm, Real.coe_toNNReal _ hβ0, Real.norm_eq_abs,
            abs_of_nonneg ENNReal.toReal_nonneg]
        exact hsum.congr fun n => (e n).symm
      exact lt_of_lt_of_le hlt hle
    have han : AnalyticOnNhd ℝ p.sum D := by
      refine p.analyticOnNhd.mono fun α hα => ?_
      rw [Metric.mem_eball, edist_dist, Real.dist_eq, sub_zero, abs_of_pos hα.1]
      exact hrad α hα
    refine (han.contDiffOn_of_completeSpace).congr fun α hα => ?_
    have hfin := h1 α hα.1.le hα.2
    rw [(hval α hα.1 hfin).1]
    show ∑' t, c t * α ^ t = FormalMultilinearSeries.ofScalarsSum c α
    rw [FormalMultilinearSeries.ofScalars_sum_eq]
    rfl


