-- Prove2me | solution 1 for ProbabilityTheory.IsCompoundPoissonDriver.ae_tendsto_arrival
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:29:24.903476+00:00
-- url     : https://prove2.me/submissions/36692221-9033-4aa5-be3f-acea94ee54fe

import Mathlib
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_isProbabilityMeasure
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_iIndepFun_interarrival
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_interarrival_pos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Filter Set Topology Complex
open scoped NNReal ENNReal BigOperators

private theorem chat19_indep_gt {Ω : Type*} [MeasurableSpace Ω]
    {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0} {ν' : Measure ℝ} {μ : Measure Ω}
    (h : IsCompoundPoissonDriver τ Y r ν' μ) :
    iIndepSet (fun n => (τ n) ⁻¹' Set.Ioi 1) μ := by
  have hτ : iIndepFun τ μ := h.iIndepFun_interarrival
  rw [iIndepSet_iff_meas_biInter fun n => (h.measurable_interarrival n) measurableSet_Ioi]
  intro s
  exact hτ.meas_biInter fun i _ => ⟨Set.Ioi 1, measurableSet_Ioi, rfl⟩

private theorem chat19_measure_gt {Ω : Type*} [MeasurableSpace Ω]
    {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0} {ν' : Measure ℝ} {μ : Measure Ω}
    (h : IsCompoundPoissonDriver τ Y r ν' μ) (n : ℕ) :
    μ ((τ n) ⁻¹' Set.Ioi 1) = expMeasure (r : ℝ) (Set.Ioi 1) := by
  rw [← Measure.map_apply (h.measurable_interarrival n) measurableSet_Ioi,
    (h.law_interarrival n).map_eq]

private theorem chat19_exp_gt {r : ℝ≥0} (hr : 0 < r) :
    expMeasure (r : ℝ) (Set.Ioi 1) ≠ 0 := by
  have hr' : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  haveI : IsProbabilityMeasure (expMeasure (r : ℝ)) := isProbabilityMeasure_expMeasure hr'
  have hcompl : Set.Ioi (1 : ℝ) = (Set.Iic 1)ᶜ := Set.compl_Iic.symm
  rw [hcompl, measure_compl measurableSet_Iic (measure_ne_top _ _), measure_univ,
    ← ofReal_cdf (expMeasure (r : ℝ)) 1, cdf_expMeasure_eq hr' 1]
  have hlt : ENNReal.ofReal (if (0 : ℝ) ≤ 1 then 1 - Real.exp (-((r : ℝ) * 1)) else 0) < 1 := by
    rw [if_pos (by norm_num : (0 : ℝ) ≤ 1), ENNReal.ofReal_lt_one]
    have := Real.exp_pos (-((r : ℝ) * 1))
    linarith
  exact (tsub_pos_iff_lt.mpr hlt).ne'

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    {τ Y : ℕ → Ω → ℝ} {r : ℝ≥0} {ν' : Measure ℝ} {μ : Measure Ω}
    (h : IsCompoundPoissonDriver τ Y r ν' μ) (hr : 0 < r) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => arrival τ n ω) atTop atTop := by
  haveI := h.isProbabilityMeasure
  have hsum : (∑' n, μ ((τ n) ⁻¹' Set.Ioi 1)) = ∞ := by
    simp_rw [chat19_measure_gt h]
    exact ENNReal.tsum_const_eq_top_of_ne_zero (chat19_exp_gt hr)
  have hlimsup : μ (limsup (fun n => (τ n) ⁻¹' Set.Ioi 1) atTop) = 1 :=
    measure_limsup_eq_one (fun n => (h.measurable_interarrival n) measurableSet_Ioi)
      (chat19_indep_gt h) hsum
  have hmeas : MeasurableSet (limsup (fun n => (τ n) ⁻¹' Set.Ioi 1) atTop) :=
    MeasurableSet.measurableSet_limsup fun n => (h.measurable_interarrival n) measurableSet_Ioi
  have hae_limsup : ∀ᵐ ω ∂μ, ω ∈ limsup (fun n => (τ n) ⁻¹' Set.Ioi 1) atTop := by
    rw [ae_iff, show {ω | ω ∉ limsup (fun n => (τ n) ⁻¹' Set.Ioi 1) atTop}
        = (limsup (fun n => (τ n) ⁻¹' Set.Ioi 1) atTop)ᶜ from rfl,
      measure_compl hmeas (measure_ne_top _ _), measure_univ, hlimsup, tsub_self]
  filter_upwards [h.ae_interarrival_pos hr, hae_limsup] with ω hpos hlim
  rw [mem_limsup_iff_frequently_mem] at hlim
  have hfreq : ∃ᶠ n in atTop, 1 < τ n ω := by
    refine hlim.mono fun n hn => ?_
    simpa [Set.mem_preimage, Set.mem_Ioi] using hn
  have hinf : {n | 1 < τ n ω}.Infinite := Nat.frequently_atTop_iff_infinite.mp hfreq
  refine tendsto_atTop_atTop_of_monotone ?_ fun b => ?_
  · exact monotone_nat_of_le_succ fun n => by
      have hstep : arrival τ (n + 1) ω = arrival τ n ω + τ (n + 1) ω := by
        simp [arrival, Finset.sum_range_succ]
      rw [hstep]
      exact le_add_of_nonneg_right (hpos (n + 1)).le
  · obtain ⟨t, hts, htcard⟩ := hinf.exists_subset_card_eq ⌈b⌉₊
    refine ⟨t.sup id, ?_⟩
    have hsubset : t ⊆ Finset.range (t.sup id + 1) := fun i hi =>
      Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))
    have h1 : (⌈b⌉₊ : ℝ) ≤ ∑ i ∈ t, τ i ω := by
      have hcard : (⌈b⌉₊ : ℝ) = ∑ _i ∈ t, (1 : ℝ) := by
        rw [Finset.sum_const, htcard, nsmul_eq_mul, mul_one]
      rw [hcard]
      exact Finset.sum_le_sum fun i hi => (le_of_lt (hts hi))
    have h2 : ∑ i ∈ t, τ i ω ≤ arrival τ (t.sup id) ω := by
      unfold arrival
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset fun i _ _ => (hpos i).le
    exact (Nat.le_ceil b).trans (h1.trans h2)