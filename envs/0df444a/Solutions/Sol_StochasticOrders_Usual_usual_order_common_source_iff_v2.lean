-- Prove2me | solution 1 for StochasticOrders.Usual.usual_order_common_source_iff_v2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-07T12:07:38.900585+00:00
-- url     : https://prove2.me/submissions/5c0fc0d5-44b2-4787-82ab-742b57c8bbe2

import Mathlib
import Definitions.Def_StochasticOrders_Usual_UsualOrder

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology

/-- Quantile function (left-continuous inverse of the cdf) of a measure on `ℝ`. -/
noncomputable def soCsrc_Q (P : Measure ℝ) (u : ℝ) : ℝ := sInf {x | u ≤ cdf P x}

theorem soCsrc_bdd (P : Measure ℝ) [IsProbabilityMeasure P] {u : ℝ} (hu0 : 0 < u) :
    BddBelow {x | u ≤ cdf P x} := by
  have h := (tendsto_cdf_atBot P).eventually (gt_mem_nhds hu0)
  rw [Filter.eventually_atBot] at h
  obtain ⟨x0, hx0⟩ := h
  refine ⟨x0, fun x hx => ?_⟩
  by_contra hlt
  exact absurd (hx0 x (le_of_lt (not_le.mp hlt))) (not_lt.mpr hx)

theorem soCsrc_nonempty (P : Measure ℝ) [IsProbabilityMeasure P] {u : ℝ} (hu1 : u < 1) :
    ({x | u ≤ cdf P x} : Set ℝ).Nonempty := by
  obtain ⟨x, hx⟩ := ((tendsto_cdf_atTop P).eventually (lt_mem_nhds hu1)).exists
  exact ⟨x, hx.le⟩

theorem soCsrc_le_cdf_Q (P : Measure ℝ) [IsProbabilityMeasure P] {u : ℝ} (hu1 : u < 1) :
    u ≤ cdf P (soCsrc_Q P u) := by
  have hcont : ContinuousWithinAt (cdf P) (Ici (soCsrc_Q P u)) (soCsrc_Q P u) :=
    (cdf P).right_continuous _
  have ht : Tendsto (cdf P) (𝓝[>] (soCsrc_Q P u)) (𝓝 (cdf P (soCsrc_Q P u))) :=
    hcont.mono Ioi_subset_Ici_self
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with x hx
  obtain ⟨s, hs, hsx⟩ := exists_lt_of_csInf_lt (soCsrc_nonempty P hu1) hx
  exact le_trans hs (monotone_cdf P hsx.le)

theorem soCsrc_Q_le_iff (P : Measure ℝ) [IsProbabilityMeasure P] {u : ℝ} (hu0 : 0 < u)
    (hu1 : u < 1) (x : ℝ) : soCsrc_Q P u ≤ x ↔ u ≤ cdf P x := by
  constructor
  · intro h
    exact le_trans (soCsrc_le_cdf_Q P hu1) (monotone_cdf P h)
  · intro h
    exact csInf_le (soCsrc_bdd P hu0) h

theorem soCsrc_Q_mono (P : Measure ℝ) [IsProbabilityMeasure P] :
    MonotoneOn (soCsrc_Q P) (Ioo 0 1) := by
  intro u hu v hv huv
  rw [soCsrc_Q_le_iff P hu.1 hu.2]
  exact le_trans huv (soCsrc_le_cdf_Q P hv.2)

instance soCsrc_U_prob : IsProbabilityMeasure (volume.restrict (Ioo (0:ℝ) 1)) :=
  ⟨by rw [Measure.restrict_apply_univ, Real.volume_Ioo]; simp⟩

theorem soCsrc_Q_ae (P : Measure ℝ) [IsProbabilityMeasure P] :
    AEMeasurable (soCsrc_Q P) (volume.restrict (Ioo (0:ℝ) 1)) :=
  aemeasurable_restrict_of_monotoneOn measurableSet_Ioo (soCsrc_Q_mono P)

theorem soCsrc_map_Q (P : Measure ℝ) [IsProbabilityMeasure P] :
    (volume.restrict (Ioo (0:ℝ) 1)).map (soCsrc_Q P) = P := by
  refine Measure.ext_of_Iic _ _ (fun x => ?_)
  rw [Measure.map_apply_of_aemeasurable (soCsrc_Q_ae P) measurableSet_Iic,
    Measure.restrict_apply' measurableSet_Ioo, ← ofReal_cdf P x]
  have hset : soCsrc_Q P ⁻¹' Iic x ∩ Ioo 0 1 = {u | u ∈ Ioo (0:ℝ) 1 ∧ u ≤ cdf P x} := by
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_Iic]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, (soCsrc_Q_le_iff P h2.1 h2.2 x).mp h1⟩
    · rintro ⟨h2, h1⟩
      exact ⟨(soCsrc_Q_le_iff P h2.1 h2.2 x).mpr h1, h2⟩
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

theorem soCsrc_cdf_le {P R : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (h : ∀ x, P (Ioi x) ≤ R (Ioi x)) (x : ℝ) : cdf R x ≤ cdf P x := by
  have hP := prob_compl_eq_one_sub (μ := P) (measurableSet_Ioi (a := x))
  have hR := prob_compl_eq_one_sub (μ := R) (measurableSet_Ioi (a := x))
  rw [compl_Ioi] at hP hR
  have key : R (Iic x) ≤ P (Iic x) := by
    rw [hP, hR]
    exact tsub_le_tsub_left (h x) 1
  rw [← ofReal_cdf, ← ofReal_cdf] at key
  exact (ENNReal.ofReal_le_ofReal_iff (cdf_nonneg P x)).mp key

theorem soCsrc_Q_le_Q {P R : Measure ℝ} [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (h : ∀ x, P (Ioi x) ≤ R (Ioi x)) {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) :
    soCsrc_Q P u ≤ soCsrc_Q R u := by
  rw [soCsrc_Q_le_iff P hu.1 hu.2]
  exact le_trans (soCsrc_le_cdf_Q R hu.2) (soCsrc_cdf_le h _)


open MeasureTheory ProbabilityTheory StochasticOrders.Usual in
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → ℝ) (Y : Ω' → ℝ) (hX : Measurable X) (hY : Measurable Y) :
    UsualOrder μ ν X Y ↔
      ∃ (S : Type) (_ : MeasurableSpace S) (Ω'' : Type) (_ : MeasurableSpace Ω'')
        (ρ : Measure Ω'') (_ : IsProbabilityMeasure ρ) (Z : Ω'' → S) (ψ1 ψ2 : S → ℝ),
        Measurable Z ∧ Measurable ψ1 ∧ Measurable ψ2 ∧
        (∀ s : S, ψ1 s ≤ ψ2 s) ∧
        IdentDistrib (ψ1 ∘ Z) X ρ μ ∧ IdentDistrib (ψ2 ∘ Z) Y ρ ν := by
  constructor
  · intro hord
    have : IsProbabilityMeasure (μ.map X) := Measure.isProbabilityMeasure_map hX.aemeasurable
    have : IsProbabilityMeasure (ν.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
    have hordP : ∀ x, μ.map X (Set.Ioi x) ≤ ν.map Y (Set.Ioi x) := by
      intro x
      rw [Measure.map_apply hX measurableSet_Ioi, Measure.map_apply hY measurableSet_Ioi]
      exact hord x
    have hXq := soCsrc_Q_ae (μ.map X)
    have hYq := soCsrc_Q_ae (ν.map Y)
    have hae : ∀ᵐ u ∂(volume.restrict (Ioo (0:ℝ) 1)), hXq.mk _ u ≤ hYq.mk _ u := by
      filter_upwards [hXq.ae_eq_mk, hYq.ae_eq_mk, ae_restrict_mem measurableSet_Ioo]
        with u h1 h2 hu
      rw [← h1, ← h2]
      exact soCsrc_Q_le_Q hordP hu
    have hmin : (fun u => min (hXq.mk _ u) (hYq.mk _ u))
        =ᵐ[volume.restrict (Ioo (0:ℝ) 1)] soCsrc_Q (μ.map X) := by
      filter_upwards [hae, hXq.ae_eq_mk] with u hu h1
      rw [min_eq_left hu, ← h1]
    have hm1 : Measurable (fun u => min (hXq.mk _ u) (hYq.mk _ u)) :=
      hXq.measurable_mk.min hYq.measurable_mk
    refine ⟨ℝ, inferInstance, ℝ, inferInstance, volume.restrict (Ioo (0:ℝ) 1), soCsrc_U_prob,
      id, fun u => min (hXq.mk _ u) (hYq.mk _ u), hYq.mk _, measurable_id, hm1,
      hYq.measurable_mk, fun s => min_le_right _ _, ?_, ?_⟩
    · refine ⟨hm1.aemeasurable, hX.aemeasurable, ?_⟩
      rw [Function.comp_id, Measure.map_congr hmin, soCsrc_map_Q]
    · refine ⟨hYq.measurable_mk.aemeasurable, hY.aemeasurable, ?_⟩
      rw [Function.comp_id, Measure.map_congr hYq.ae_eq_mk.symm, soCsrc_map_Q]
  · rintro ⟨S, _, Ω'', _, ρ, _, Z, ψ1, ψ2, hZ, h1m, h2m, hle, hXd, hYd⟩ t
    calc μ {ω | t < X ω} = ρ {u | t < (ψ1 ∘ Z) u} :=
          (hXd.measure_mem_eq (measurableSet_Ioi (a := t))).symm
      _ ≤ ρ {u | t < (ψ2 ∘ Z) u} := by
          apply measure_mono
          intro u hu
          exact lt_of_lt_of_le hu (hle (Z u))
      _ = ν {ω | t < Y ω} := hYd.measure_mem_eq (measurableSet_Ioi (a := t))
