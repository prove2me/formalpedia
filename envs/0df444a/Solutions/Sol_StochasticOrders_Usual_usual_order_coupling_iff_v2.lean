-- Prove2me | solution 1 for StochasticOrders.Usual.usual_order_coupling_iff_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T05:30:52.129407+00:00
-- url     : https://prove2.me/submissions/71dfc543-1f85-49a6-bfa3-2af2b95e953e

import Mathlib
import Definitions.Def_StochasticOrders_Usual_UsualOrder

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology

/-- Quantile function (left-continuous inverse of the cdf) of a measure on `ℝ`. -/
noncomputable def soCpl_Q (P : Measure ℝ) (u : ℝ) : ℝ := sInf {x | u ≤ cdf P x}

theorem soCpl_bdd (P : Measure ℝ) [IsProbabilityMeasure P] {u : ℝ} (hu0 : 0 < u) :
    BddBelow {x | u ≤ cdf P x} := by
  have h := (tendsto_cdf_atBot P).eventually (gt_mem_nhds hu0)
  rw [Filter.eventually_atBot] at h
  obtain ⟨x0, hx0⟩ := h
  refine ⟨x0, fun x hx => ?_⟩
  by_contra hlt
  exact absurd (hx0 x (le_of_lt (not_le.mp hlt))) (not_lt.mpr hx)

theorem soCpl_nonempty (P : Measure ℝ) [IsProbabilityMeasure P] {u : ℝ} (hu1 : u < 1) :
    ({x | u ≤ cdf P x} : Set ℝ).Nonempty := by
  obtain ⟨x, hx⟩ := ((tendsto_cdf_atTop P).eventually (lt_mem_nhds hu1)).exists
  exact ⟨x, hx.le⟩

theorem soCpl_le_cdf_Q (P : Measure ℝ) [IsProbabilityMeasure P] {u : ℝ} (hu1 : u < 1) :
    u ≤ cdf P (soCpl_Q P u) := by
  have hcont : ContinuousWithinAt (cdf P) (Ici (soCpl_Q P u)) (soCpl_Q P u) :=
    (cdf P).right_continuous _
  have ht : Tendsto (cdf P) (𝓝[>] (soCpl_Q P u)) (𝓝 (cdf P (soCpl_Q P u))) :=
    hcont.mono Ioi_subset_Ici_self
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with x hx
  obtain ⟨s, hs, hsx⟩ := exists_lt_of_csInf_lt (soCpl_nonempty P hu1) hx
  exact le_trans hs (monotone_cdf P hsx.le)

theorem soCpl_Q_le_iff (P : Measure ℝ) [IsProbabilityMeasure P] {u : ℝ} (hu0 : 0 < u)
    (hu1 : u < 1) (x : ℝ) : soCpl_Q P u ≤ x ↔ u ≤ cdf P x := by
  constructor
  · intro h
    exact le_trans (soCpl_le_cdf_Q P hu1) (monotone_cdf P h)
  · intro h
    exact csInf_le (soCpl_bdd P hu0) h

theorem soCpl_Q_mono (P : Measure ℝ) [IsProbabilityMeasure P] :
    MonotoneOn (soCpl_Q P) (Ioo 0 1) := by
  intro u hu v hv huv
  rw [soCpl_Q_le_iff P hu.1 hu.2]
  exact le_trans huv (soCpl_le_cdf_Q P hv.2)

instance soCpl_U_prob : IsProbabilityMeasure (volume.restrict (Ioo (0:ℝ) 1)) :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioo]; simp⟩

theorem soCpl_Q_ae (P : Measure ℝ) [IsProbabilityMeasure P] :
    AEMeasurable (soCpl_Q P) (volume.restrict (Ioo (0:ℝ) 1)) :=
  aemeasurable_restrict_of_monotoneOn measurableSet_Ioo (soCpl_Q_mono P)

theorem soCpl_map_Q (P : Measure ℝ) [IsProbabilityMeasure P] :
    (volume.restrict (Ioo (0:ℝ) 1)).map (soCpl_Q P) = P := by
  refine Measure.ext_of_Iic _ _ (fun x => ?_)
  rw [Measure.map_apply_of_aemeasurable (soCpl_Q_ae P) measurableSet_Iic,
    Measure.restrict_apply' measurableSet_Ioo, ← ofReal_cdf P x]
  have hset : soCpl_Q P ⁻¹' Iic x ∩ Ioo 0 1 = {u | u ∈ Ioo (0:ℝ) 1 ∧ u ≤ cdf P x} := by
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_Iic]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, (soCpl_Q_le_iff P h2.1 h2.2 x).mp h1⟩
    · rintro ⟨h2, h1⟩
      exact ⟨(soCpl_Q_le_iff P h2.1 h2.2 x).mpr h1, h2⟩
  rw [hset]
  apply le_antisymm
  · calc volume {u | u ∈ Ioo (0:ℝ) 1 ∧ u ≤ cdf P x} ≤ volume (Icc 0 (cdf P x)) :=
          measure_mono (fun u hu => ⟨hu.1.1.le, hu.2⟩)
      _ = ENNReal.ofReal (cdf P x) := by rw [Real.volume_Icc, sub_zero]
  · calc ENNReal.ofReal (cdf P x) = volume (Ioo 0 (cdf P x)) := by rw [Real.volume_Ioo, sub_zero]
      _ ≤ volume {u | u ∈ Ioo (0:ℝ) 1 ∧ u ≤ cdf P x} := by
          apply measure_mono
          intro u hu
          exact ⟨⟨hu.1, lt_of_lt_of_le hu.2 (cdf_le_one P x)⟩, hu.2.le⟩

theorem soCpl_cdf_le {P R : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (h : ∀ x, P (Ioi x) ≤ R (Ioi x)) (x : ℝ) : cdf R x ≤ cdf P x := by
  have hP := prob_compl_eq_one_sub (μ := P) (measurableSet_Ioi (a := x))
  have hR := prob_compl_eq_one_sub (μ := R) (measurableSet_Ioi (a := x))
  rw [compl_Ioi] at hP hR
  have key : R (Iic x) ≤ P (Iic x) := by
    rw [hP, hR]
    exact tsub_le_tsub_left (h x) 1
  rw [← ofReal_cdf, ← ofReal_cdf] at key
  exact (ENNReal.ofReal_le_ofReal_iff (cdf_nonneg P x)).mp key

theorem soCpl_Q_le_Q {P R : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (h : ∀ x, P (Ioi x) ≤ R (Ioi x)) {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) :
    soCpl_Q P u ≤ soCpl_Q R u := by
  rw [soCpl_Q_le_iff P hu.1 hu.2]
  exact le_trans (soCpl_le_cdf_Q R hu.2) (soCpl_cdf_le h _)


open MeasureTheory ProbabilityTheory StochasticOrders.Usual in
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y) :
    UsualOrder μ ν X Y ↔
      ∃ (Ω'' : Type) (_ : MeasurableSpace Ω'') (ρ : Measure Ω'') (_ : IsProbabilityMeasure ρ)
        (Xhat Yhat : Ω'' → ℝ),
        Measurable Xhat ∧ Measurable Yhat ∧
        IdentDistrib Xhat X ρ μ ∧ IdentDistrib Yhat Y ρ ν ∧ ρ {ω | Xhat ω ≤ Yhat ω} = 1 := by
  constructor
  · intro hord
    have : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
    have : IsProbabilityMeasure (ν.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
    have hordP : ∀ x, μ.map X (Set.Ioi x) ≤ ν.map Y (Set.Ioi x) := by
      intro x
      rw [Measure.map_apply hX measurableSet_Ioi, Measure.map_apply hY measurableSet_Ioi]
      exact hord x
    set ρ : Measure ℝ := volume.restrict (Ioo (0:ℝ) 1) with hρ
    have hXq := soCpl_Q_ae (μ.map X)
    have hYq := soCpl_Q_ae (ν.map Y)
    refine ⟨ℝ, inferInstance, ρ, soCpl_U_prob, hXq.mk _, hYq.mk _, hXq.measurable_mk,
      hYq.measurable_mk, ?_, ?_, ?_⟩
    · refine ⟨hXq.measurable_mk.aemeasurable, hX.aemeasurable, ?_⟩
      rw [Measure.map_congr hXq.ae_eq_mk.symm, soCpl_map_Q]
    · refine ⟨hYq.measurable_mk.aemeasurable, hY.aemeasurable, ?_⟩
      rw [Measure.map_congr hYq.ae_eq_mk.symm, soCpl_map_Q]
    · have hae : ∀ᵐ u ∂ρ, hXq.mk _ u ≤ hYq.mk _ u := by
        filter_upwards [hXq.ae_eq_mk, hYq.ae_eq_mk, ae_restrict_mem measurableSet_Ioo]
          with u h1 h2 hu
        rw [← h1, ← h2]
        exact soCpl_Q_le_Q hordP hu
      have hms : MeasurableSet {u | hXq.mk _ u ≤ hYq.mk _ u} :=
        measurableSet_le hXq.measurable_mk hYq.measurable_mk
      rw [← prob_compl_eq_zero_iff hms]
      exact ae_iff.mp hae
  · rintro ⟨Ω'', _, ρ, _, Xh, Yh, hXm, hYm, hXd, hYd, h1⟩ t
    have hms : MeasurableSet {u | Xh u ≤ Yh u} := measurableSet_le hXm hYm
    have hae : ∀ᵐ u ∂ρ, Xh u ≤ Yh u := ae_iff.mpr ((prob_compl_eq_zero_iff hms).mpr h1)
    calc μ {ω | t < X ω} = ρ {u | t < Xh u} :=
          (hXd.measure_mem_eq (measurableSet_Ioi (a := t))).symm
      _ ≤ ρ {u | t < Yh u} := by
          apply measure_mono_ae
          filter_upwards [hae] with u hu htu
          exact lt_of_lt_of_le htu hu
      _ = ν {ω | t < Y ω} := hYd.measure_mem_eq (measurableSet_Ioi (a := t))
