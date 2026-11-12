-- Prove2me | solution 1 for PersuasionByParts.Known.joint_cutoff_value
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T17:00:41.56355+00:00
-- url     : https://prove2.me/submissions/a8c1a89d-0dcf-4f22-a23a-e36b1f652a06

import Mathlib
import Definitions.Def_PersuasionByParts_Known_Pooling

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
noncomputable section

namespace PersuasionByParts.Known.Dev.PoolQ
open PersuasionByParts.Known

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

/-- Galois connection characterising the quantile on `(0,1)`. -/
theorem exists_galois {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) :
    ∃ a : ℝ, (∀ t, u ≤ cdf μ t ↔ a ≤ t) ∧ quantile μ u = a := by
  set S : Set ℝ := {t | u ≤ cdf μ t} with hS
  have hmono : Monotone (cdf μ) := (cdf μ).mono
  have hne : S.Nonempty := by
    have := (tendsto_cdf_atTop μ).eventually (eventually_ge_nhds hu.2)
    obtain ⟨t, ht⟩ := this.exists
    exact ⟨t, ht⟩
  have hbdd : BddBelow S := by
    have := (tendsto_cdf_atBot μ).eventually (eventually_lt_nhds hu.1)
    obtain ⟨b, hb⟩ := eventually_atBot.1 this
    refine ⟨b, fun t ht => ?_⟩
    by_contra h
    push Not at h
    exact absurd (hb t h.le) (not_lt.2 ht)
  set a := sInf S with ha
  have haS : a ∈ S := by
    have hcont : ContinuousWithinAt (cdf μ) (Ioi a) a := ((cdf μ).right_continuous a).mono Ioi_subset_Ici_self
    have hmem : ∀ n : ℕ, a + 1 / ((n:ℝ) + 1) ∈ S := by
      intro n
      have : a < a + 1 / ((n:ℝ) + 1) := by
        have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
        linarith
      obtain ⟨s, hs, hlt⟩ := exists_lt_of_csInf_lt hne this
      exact le_trans hs (hmono hlt.le)
    have hlim : Tendsto (fun n : ℕ => a + 1 / ((n:ℝ) + 1)) atTop (𝓝[>] a) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
      · simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_add a
      · have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
        simp only [mem_Ioi]; linarith
    have h2 := hcont.tendsto.comp hlim
    exact ge_of_tendsto' h2 (fun n => hmem n)
  have hgal : ∀ t, u ≤ cdf μ t ↔ a ≤ t := fun t =>
    ⟨fun h => csInf_le hbdd h, fun h => le_trans haS (hmono h)⟩
  refine ⟨a, hgal, ?_⟩
  unfold quantile PersuasionNetworks.stateQuantile
  have : ((fun t : ℝ => (t : EReal)) '' {t ∈ (Set.univ : Set ℝ) | u ≤ cdf μ t}) =
      (fun t : ℝ => (t : EReal)) '' Ici a := by
    congr 1
    ext t; simp [hgal]
  rw [this]
  have hl : IsLeast ((fun t : ℝ => (t : EReal)) '' Ici a) (a : EReal) :=
    ⟨⟨a, (mem_Ici.2 le_rfl), rfl⟩, by
      rintro _ ⟨t, ht, rfl⟩
      exact EReal.coe_le_coe_iff.2 ht⟩
  rw [hl.csInf_eq]; rfl

theorem quantile_le_iff {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) (t : ℝ) :
    quantile μ u ≤ t ↔ u ≤ cdf μ t := by
  obtain ⟨a, h, rfl⟩ := exists_galois μ hu
  exact (h t).symm

theorem monotoneOn_quantile : MonotoneOn (quantile μ) (Ioo 0 1) := by
  intro u hu v hv huv
  rw [quantile_le_iff μ hu]
  exact le_trans huv ((quantile_le_iff μ hv _).1 le_rfl)

theorem le_cdf_quantile {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) : u ≤ cdf μ (quantile μ u) :=
  (quantile_le_iff μ hu _).1 le_rfl


theorem aemeasurable_quantile : AEMeasurable (quantile μ) (volume.restrict (Ioo (0:ℝ) 1)) :=
  aemeasurable_restrict_of_monotoneOn measurableSet_Ioo (monotoneOn_quantile μ)

theorem map_quantile :
    (volume.restrict (Ioo (0:ℝ) 1)).map (quantile μ) = μ := by
  haveI : IsProbabilityMeasure (volume.restrict (Ioo (0:ℝ) 1)) :=
    ⟨by simp⟩
  haveI : IsProbabilityMeasure ((volume.restrict (Ioo (0:ℝ) 1)).map (quantile μ)) :=
    Measure.isProbabilityMeasure_map (aemeasurable_quantile μ)
  refine Measure.ext_of_Iic _ _ fun t => ?_
  rw [Measure.map_apply_of_aemeasurable (aemeasurable_quantile μ) measurableSet_Iic,
    Measure.restrict_apply' measurableSet_Ioo]
  have hc0 := cdf_nonneg μ t
  have hc1 := cdf_le_one μ t
  have hset : quantile μ ⁻¹' Iic t ∩ Ioo 0 1 = Ioo (0:ℝ) 1 ∩ Iic (cdf μ t) := by
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_Iic]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, (quantile_le_iff μ h2 t).1 h1⟩
    · rintro ⟨h2, h1⟩; exact ⟨(quantile_le_iff μ h2 t).2 h1, h2⟩
  rw [hset]
  have hr : μ (Iic t) = ENNReal.ofReal (cdf μ t) := by
    rw [cdf_eq_real, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  rw [hr]
  apply le_antisymm
  · calc volume (Ioo (0:ℝ) 1 ∩ Iic (cdf μ t)) ≤ volume (Ioc 0 (cdf μ t)) :=
          measure_mono (fun u hu => ⟨hu.1.1, hu.2⟩)
      _ = _ := by simp [Real.volume_Ioc]
  · calc ENNReal.ofReal (cdf μ t) = volume (Ioo 0 (cdf μ t)) := by simp [Real.volume_Ioo]
      _ ≤ volume (Ioo (0:ℝ) 1 ∩ Iic (cdf μ t)) := measure_mono (fun u hu => ⟨⟨hu.1, lt_of_lt_of_le hu.2 hc1⟩, hu.2.le⟩)

/-- Transfer of integrals from the quantile coordinate to `μ`. -/
theorem integral_quantile (f : ℝ → ℝ) (hf : AEStronglyMeasurable f μ) :
    ∫ z, f z ∂μ = ∫ u in Ioo (0:ℝ) 1, f (quantile μ u) := by
  conv_lhs => rw [← map_quantile μ]
  rw [integral_map (aemeasurable_quantile μ) (by rwa [map_quantile μ])]

theorem integrable_quantile_iff (f : ℝ → ℝ) (hf : AEStronglyMeasurable f μ) :
    Integrable (fun u => f (quantile μ u)) (volume.restrict (Ioo (0:ℝ) 1)) ↔ Integrable f μ := by
  conv_rhs => rw [← map_quantile μ]
  rw [integrable_map_measure (by rwa [map_quantile μ]) (aemeasurable_quantile μ)]
  rfl

end PersuasionByParts.Known.Dev.PoolQ
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
noncomputable section

namespace PersuasionByParts.Known.Dev.Pool
open PersuasionByParts.Known PersuasionByParts.Known.Dev.PoolQ

variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

theorem integrableOn_Q (hμ : Integrable id μ) :
    IntegrableOn (quantile μ) (Ioo (0:ℝ) 1) := by
  have := (integrable_quantile_iff μ id aestronglyMeasurable_id).2 hμ
  exact this

theorem intervalIntegrable_Q (hμ : Integrable id μ) {a b : ℝ} (ha : a ∈ Icc (0:ℝ) 1) (hb : b ∈ Icc (0:ℝ) 1) :
    IntervalIntegrable (quantile μ) volume a b := by
  have h1 := integrableOn_Q μ hμ
  have h2 : IntegrableOn (quantile μ) (Icc 0 1) :=
    (integrableOn_Icc_iff_integrableOn_Ioo).2 h1
  refine IntervalIntegrable.mono_set (a := 0) (b := 1) ?_ ?_
  · exact (intervalIntegrable_iff_integrableOn_Icc_of_le zero_le_one).2 h2
  · rw [uIcc_of_le zero_le_one]
    exact uIcc_subset_Icc ha hb

theorem G_eq (s : ℝ) : poolMean μ s = (∫ u in (1 - s)..1, quantile μ u) / s := rfl


theorem poolMean_one' (hμ : Integrable id μ) : poolMean μ 1 = ∫ x, x ∂μ := by
  rw [G_eq]
  simp only [sub_self, div_one]
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  exact (integral_quantile μ id aestronglyMeasurable_id).symm

theorem mul_Q_le_G (hμ : Integrable id μ) {s : ℝ} (hs : s ∈ Ioo (0:ℝ) 1) :
    s * quantile μ (1 - s) ≤ ∫ u in (1 - s)..1, quantile μ u := by
  have h1 : (1 - s) ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) (a := 1 - s) (b := 1)
    (f := fun _ => quantile μ (1 - s)) (g := quantile μ) (by linarith [hs.1])
    intervalIntegrable_const
    (intervalIntegrable_Q μ hμ ⟨by linarith [hs.2], by linarith [hs.1]⟩ ⟨zero_le_one, le_rfl⟩)
    (fun u hu => monotoneOn_quantile μ h1 ⟨by linarith [hu.1, hs.2], hu.2⟩ hu.1.le)
  simpa [mul_comm] using this

theorem poolMean_antitoneOn' (hμ : Integrable id μ) : AntitoneOn (poolMean μ) (Ioc 0 1) := by
  intro s hs s' hs' hss'
  rcases hss'.eq_or_lt with rfl | hlt
  · exact le_rfl
  have hsO : s ∈ Ioo (0:ℝ) 1 := ⟨hs.1, by linarith [hs'.2]⟩
  have hy : (1 - s) ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hs'.2], by linarith [hs.1]⟩
  have hint := fun (a b : ℝ) (ha : a ∈ Icc (0:ℝ) 1) (hb : b ∈ Icc (0:ℝ) 1) =>
    intervalIntegrable_Q μ hμ ha hb
  have hsplit : ∫ u in (1 - s')..1, quantile μ u =
      (∫ u in (1 - s')..(1 - s), quantile μ u) + ∫ u in (1 - s)..1, quantile μ u := by
    rw [intervalIntegral.integral_add_adjacent_intervals]
    · exact hint _ _ ⟨by linarith [hs'.1, hs'.2], by linarith [hs'.1, hs'.2]⟩ ⟨by linarith [hs.2, hs'.2], by linarith [hs.1]⟩
    · exact hint _ _ ⟨by linarith [hs.2, hs'.2], by linarith [hs.1]⟩ ⟨zero_le_one, le_rfl⟩
  have hA : ∫ u in (1 - s')..(1 - s), quantile μ u ≤ (s' - s) * quantile μ (1 - s) := by
    have := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) (a := 1 - s') (b := 1 - s)
      (f := quantile μ) (g := fun _ => quantile μ (1 - s)) (by linarith)
      (hint _ _ ⟨by linarith [hs'.1, hs'.2], by linarith [hs'.1, hs'.2]⟩ ⟨by linarith [hs.2, hs'.2], by linarith [hs.1]⟩)
      intervalIntegrable_const
      (fun u hu => monotoneOn_quantile μ ⟨by linarith [hu.1, hs'.2], by linarith [hu.2, hs.1]⟩ hy hu.2.le)
    simpa [mul_comm, sub_sub_sub_cancel_left] using this
  have hB := mul_Q_le_G μ hμ hsO
  rw [G_eq, G_eq, div_le_div_iff₀ hs'.1 hs.1, hsplit]
  have h1 : 0 < s := hs.1
  have h2 : 0 < s' - s := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hA h1.le, mul_le_mul_of_nonneg_left hB h2.le]

theorem poolMean_continuousOn' (hμ : Integrable id μ) : ContinuousOn (poolMean μ) (Ioc 0 1) := by
  have hint : IntegrableOn (quantile μ) (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact (integrableOn_Icc_iff_integrableOn_Ioo).2 (integrableOn_Q μ hμ)
  have hF := intervalIntegral.continuousOn_primitive_interval (μ := volume) hint
  have hG : ContinuousOn (fun s : ℝ => ∫ u in (1 - s)..1, quantile μ u) (Ioc 0 1) := by
    have e : ∀ s ∈ Ioc (0:ℝ) 1, (∫ u in (1 - s)..1, quantile μ u) =
        (∫ u in (0:ℝ)..1, quantile μ u) - ∫ u in (0:ℝ)..(1 - s), quantile μ u := fun s hs =>
      (intervalIntegral.integral_interval_sub_left
        (intervalIntegrable_Q μ hμ ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩)
        (intervalIntegrable_Q μ hμ ⟨le_rfl, zero_le_one⟩
          ⟨by linarith [hs.2], by linarith [hs.1]⟩)).symm
    refine ContinuousOn.congr (f := fun s : ℝ => (∫ u in (0:ℝ)..1, quantile μ u) -
      ∫ u in (0:ℝ)..(1 - s), quantile μ u) ?_ e
    refine continuousOn_const.sub (hF.comp (by fun_prop) fun s hs => ?_)
    rw [uIcc_of_le zero_le_one]
    exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
  exact hG.div continuousOn_id (fun s hs => hs.1.ne')


theorem mu_eq_vol {B : Set ℝ} (hB : MeasurableSet B) :
    μ B = volume (quantile μ ⁻¹' B ∩ Ioo (0:ℝ) 1) := by
  conv_lhs => rw [← map_quantile μ]
  rw [Measure.map_apply_of_aemeasurable (aemeasurable_quantile μ) hB,
    Measure.restrict_apply' measurableSet_Ioo]

theorem real_Ioi_le {s : ℝ} (hs : s ∈ Ioo (0:ℝ) 1) :
    μ.real (Ioi (quantile μ (1 - s))) ≤ s := by
  have h1 : (1 - s) ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  rw [← compl_Iic, probReal_compl_eq_one_sub measurableSet_Iic, ← cdf_eq_real]
  linarith [le_cdf_quantile μ h1]

theorem le_real_Ici {s : ℝ} (hs : s ∈ Ioo (0:ℝ) 1) :
    s ≤ μ.real (Ici (quantile μ (1 - s))) := by
  have h1 : (1 - s) ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  rw [← compl_Iio, probReal_compl_eq_one_sub measurableSet_Iio]
  have : μ (Iio (quantile μ (1 - s))) ≤ ENNReal.ofReal (1 - s) := by
    rw [mu_eq_vol μ measurableSet_Iio]
    calc volume (quantile μ ⁻¹' Iio (quantile μ (1 - s)) ∩ Ioo (0:ℝ) 1)
        ≤ volume (Ioo (0:ℝ) (1 - s)) := by
          refine measure_mono fun u hu => ⟨hu.2.1, ?_⟩
          by_contra hcon
          push Not at hcon
          exact absurd (monotoneOn_quantile μ h1 hu.2 hcon) (not_le.2 hu.1)
      _ = _ := by simp
  have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top this
  rw [ENNReal.toReal_ofReal (by linarith [hs.2])] at h2
  rw [measureReal_def]
  linarith


theorem top_eq {s : ℝ} (hs : s ∈ Ioo (0:ℝ) 1) (z : ℝ) :
    topSelector μ s z = (Ioi (quantile μ (1 - s))).indicator (fun _ => (1:ℝ)) z +
      atomFraction μ s * ({quantile μ (1 - s)} : Set ℝ).indicator (fun _ => (1:ℝ)) z := by
  have h0 : ¬ s ≤ 0 := not_le.2 hs.1
  have h1 : ¬ 1 ≤ s := not_le.2 hs.2
  unfold topSelector
  rw [if_neg h0, if_neg h1]
  rcases lt_trichotomy z (quantile μ (1 - s)) with h | h | h
  · simp [h, h.ne, not_lt.2 h.le]
  · subst h; simp
  · simp [h, h.ne', not_lt.2 h.le]

theorem atom_spec {s : ℝ} (hs : s ∈ Ioo (0:ℝ) 1) :
    0 ≤ atomFraction μ s ∧ atomFraction μ s ≤ 1 ∧
    μ.real (Ioi (quantile μ (1 - s))) + atomFraction μ s * μ.real {quantile μ (1 - s)} = s := by
  set a := quantile μ (1 - s) with ha
  have hI := real_Ioi_le μ hs
  have hC := le_real_Ici μ hs
  have hU : μ.real (Ici a) = μ.real {a} + μ.real (Ioi a) := by
    have : Ici a = {a} ∪ Ioi a := by
      ext x; simp [le_iff_eq_or_lt, eq_comm]
    rw [this]
    exact measureReal_union (by simp) measurableSet_Ioi
  have hpos : 0 ≤ μ.real {a} := measureReal_nonneg
  unfold atomFraction
  simp only [← ha]
  by_cases h : μ.real {a} = 0
  · rw [if_pos h]
    refine ⟨le_rfl, zero_le_one, ?_⟩
    rw [h] at hU; simp only [h]; linarith
  · rw [if_neg h]
    have hp : 0 < μ.real {a} := lt_of_le_of_ne hpos (Ne.symm h)
    have hI0 : 0 ≤ μ.real (Ioi a) := measureReal_nonneg
    refine ⟨div_nonneg (by linarith) hp.le, (div_le_one hp).2 (by linarith), ?_⟩
    field_simp; ring


theorem restrict_top {s : ℝ} (hs : s ∈ Ioo (0:ℝ) 1) (h : ℝ → ℝ)
    (hv : ∀ z, z ≤ quantile μ (1 - s) → h z = 0) (hm : AEStronglyMeasurable h μ) :
    ∫ u in Ioo (1 - s) 1, h (quantile μ u) = ∫ z, h z ∂μ := by
  have h1 : (1 - s) ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  rw [integral_quantile μ h hm]
  symm
  refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioo
    (Ioo_subset_Ioo h1.1.le le_rfl) fun u hu => ?_
  apply hv
  have : u ≤ 1 - s := by
    by_contra hc; push Not at hc; exact hu.2 ⟨hc, hu.1.2⟩
  exact monotoneOn_quantile μ hu.1 h1 this

theorem G_split (hμ : Integrable id μ) {s : ℝ} (hs : s ∈ Ioo (0:ℝ) 1) :
    ∫ u in (1 - s)..1, quantile μ u =
      (∫ z, (Ioi (quantile μ (1 - s))).indicator id z ∂μ) +
        quantile μ (1 - s) * (s - μ.real (Ioi (quantile μ (1 - s)))) := by
  set a := quantile μ (1 - s) with ha
  have h1 : (1 - s) ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hsub : Ioo (1 - s) 1 ⊆ Ioo (0:ℝ) 1 := Ioo_subset_Ioo h1.1.le le_rfl
  have hfi : Integrable ((Ioi a).indicator (id : ℝ → ℝ)) μ := hμ.indicator measurableSet_Ioi
  have h1i : Integrable ((Ioi a).indicator (fun _ : ℝ => (1:ℝ))) μ :=
    (integrable_const (1:ℝ)).indicator measurableSet_Ioi
  have hfQ : IntegrableOn (fun u => (Ioi a).indicator (id : ℝ → ℝ) (quantile μ u)) (Ioo (1 - s) 1) :=
    ((integrable_quantile_iff μ _ hfi.1).2 hfi).mono_measure (Measure.restrict_mono hsub le_rfl)
  have h1Q : IntegrableOn (fun u => (Ioi a).indicator (fun _ : ℝ => (1:ℝ)) (quantile μ u))
      (Ioo (1 - s) 1) :=
    ((integrable_quantile_iff μ _ h1i.1).2 h1i).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hpt : ∀ u ∈ Ioo (1 - s) 1, quantile μ u =
      (Ioi a).indicator (id : ℝ → ℝ) (quantile μ u) +
        a * (1 - (Ioi a).indicator (fun _ : ℝ => (1:ℝ)) (quantile μ u)) := by
    intro u hu
    have hge : a ≤ quantile μ u := monotoneOn_quantile μ h1 ⟨by linarith [hu.1, hs.2], hu.2⟩ hu.1.le
    rcases hge.eq_or_lt with h | h
    · rw [← h]; simp
    · simp [h]
  rw [intervalIntegral.integral_of_le (by linarith [hs.1]), integral_Ioc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo hpt]
  have hc : IntegrableOn (fun _ : ℝ => (1:ℝ)) (Ioo (1 - s) 1) :=
    integrableOn_const (by simp) (by simp)
  have hg : IntegrableOn (fun u => a * (1 - (Ioi a).indicator (fun _ : ℝ => (1:ℝ)) (quantile μ u)))
      (Ioo (1 - s) 1) := (hc.sub h1Q).const_mul a
  have hg2 : ∫ u in Ioo (1 - s) 1, (1 - (Ioi a).indicator (fun _ : ℝ => (1:ℝ)) (quantile μ u)) =
      s - ∫ u in Ioo (1 - s) 1, (Ioi a).indicator (fun _ : ℝ => (1:ℝ)) (quantile μ u) := by
    rw [integral_sub hc h1Q]; simp; linarith [hs.1]
  rw [integral_add hfQ hg, integral_const_mul, hg2]
  rw [restrict_top μ hs _ (fun z hz => by have hz' : z ≤ a := hz; simp [not_lt.2 hz']) hfi.1,
    restrict_top μ hs (fun z => (Ioi a).indicator (fun _ : ℝ => (1:ℝ)) z)
      (fun z hz => by have hz' : z ≤ a := hz; simp [not_lt.2 hz']) h1i.1]
  simp [integral_indicator measurableSet_Ioi, measureReal_def]


theorem top_mem {s : ℝ} (hs : s ∈ Ioo (0:ℝ) 1) (z : ℝ) : topSelector μ s z ∈ Icc (0:ℝ) 1 := by
  obtain ⟨c0, c1, -⟩ := atom_spec μ hs
  rw [top_eq μ hs]
  by_cases h1 : quantile μ (1 - s) < z
  · simp [h1, h1.ne']
  · by_cases h2 : z = quantile μ (1 - s)
    · simp [h2]; exact ⟨c0, c1⟩
    · simp [h1, h2]

theorem top_spec (hμ : Integrable id μ) {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    (∀ z : ℝ, topSelector μ s z ∈ Icc (0:ℝ) 1) ∧ (∫ z, topSelector μ s z ∂μ) = s ∧
    (∫ z, topSelector μ s z * z ∂μ) = s * poolMean μ s := by
  rcases hs.1.eq_or_lt with h0 | h0
  · subst h0
    have : ∀ z, topSelector μ 0 z = 0 := fun z => by simp [topSelector]
    simp [this, poolMean]
  rcases hs.2.eq_or_lt with h1 | h1
  · subst h1
    have : ∀ z, topSelector μ 1 z = 1 := fun z => by simp [topSelector]
    simp [this, poolMean_one' μ hμ]
  have hs' : s ∈ Ioo (0:ℝ) 1 := ⟨h0, h1⟩
  obtain ⟨-, -, h⟩ := atom_spec μ hs'
  set a := quantile μ (1 - s) with ha
  set c := atomFraction μ s with hc
  have hi1 : Integrable ((Ioi a).indicator (fun _ : ℝ => (1:ℝ))) μ :=
    (integrable_const (1:ℝ)).indicator measurableSet_Ioi
  have hi2 : Integrable (({a} : Set ℝ).indicator (fun _ : ℝ => (1:ℝ))) μ :=
    (integrable_const (1:ℝ)).indicator (measurableSet_singleton a)
  have hfi : Integrable ((Ioi a).indicator (id : ℝ → ℝ)) μ := hμ.indicator measurableSet_Ioi
  have hI1 : ∫ z, (Ioi a).indicator (fun _ : ℝ => (1:ℝ)) z ∂μ = μ.real (Ioi a) := by
    simp [integral_indicator measurableSet_Ioi, measureReal_def]
  have hI2 : ∫ z, ({a} : Set ℝ).indicator (fun _ : ℝ => (1:ℝ)) z ∂μ = μ.real {a} := by
    rw [integral_indicator_const _ (measurableSet_singleton a)]; simp
  refine ⟨top_mem μ hs', ?_, ?_⟩
  · simp_rw [top_eq μ hs']
    rw [integral_add hi1 (hi2.const_mul c), integral_const_mul, hI1, hI2]
    exact h
  · have e : ∀ z, topSelector μ s z * z = (Ioi a).indicator (id : ℝ → ℝ) z +
        (c * a) * ({a} : Set ℝ).indicator (fun _ : ℝ => (1:ℝ)) z := by
      intro z
      rw [top_eq μ hs', ← ha, ← hc]
      simp only [Set.indicator_apply, mem_Ioi, mem_singleton_iff]
      rcases lt_trichotomy z a with h | h | h
      · simp [h, h.ne, not_lt.2 h.le]
      · subst h; simp
      · simp [h, h.ne', not_lt.2 h.le]
    simp_rw [e]
    rw [integral_add hfi (hi2.const_mul _), integral_const_mul, hI2]
    have hG : s * poolMean μ s = ∫ u in (1 - s)..1, quantile μ u := by
      rw [G_eq, mul_div_cancel₀ _ h0.ne']
    rw [hG, G_split μ hμ hs']
    have : s - μ.real (Ioi a) = c * μ.real {a} := by linarith
    rw [this]; ring


theorem bathtub (hμ : Integrable id μ) {w : ℝ → ℝ} (hw : Measurable w)
    (hw01 : ∀ z, w z ∈ Icc (0:ℝ) 1) {s : ℝ} (hs : s ∈ Ioc (0:ℝ) 1) (hmass : ∫ z, w z ∂μ = s)
    {f : ℝ → ℝ} (hf : Monotone f) (hfi : Integrable f μ) :
    ∫ z, w z * f z ∂μ ≤ ∫ z, topSelector μ s z * f z ∂μ := by
  have hwi : Integrable w μ := Integrable.of_bound hw.aestronglyMeasurable 1
    (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [(hw01 z).1], (hw01 z).2⟩)
  have hT := measurable_topSelector μ s
  have hs1 : s ∈ Icc (0:ℝ) 1 := ⟨hs.1.le, hs.2⟩
  obtain ⟨hTmem, hTint, -⟩ := top_spec μ hμ hs1
  have hTi : Integrable (topSelector μ s) μ := Integrable.of_bound hT.aestronglyMeasurable 1
    (Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [(hTmem z).1], (hTmem z).2⟩)
  have hwf : Integrable (fun z => w z * f z) μ := by
    refine Integrable.bdd_mul hfi hw.aestronglyMeasurable (c := 1) (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [(hw01 z).1], (hw01 z).2⟩
  have hTf : Integrable (fun z => topSelector μ s z * f z) μ := by
    refine Integrable.bdd_mul hfi hT.aestronglyMeasurable (c := 1) (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [(hTmem z).1], (hTmem z).2⟩
  rcases hs.2.eq_or_lt with rfl | h1
  · have hT1 : ∀ z, topSelector μ 1 z = 1 := fun z => by simp [topSelector]
    simp_rw [hT1]
    have hz : ∀ᵐ z ∂μ, w z = 1 := by
      have h0 : ∫ z, (1 - w z) ∂μ = 0 := by
        rw [integral_sub (integrable_const _) hwi, hmass]; simp
      have := (integral_eq_zero_iff_of_nonneg (fun z => by show (0:ℝ) ≤ 1 - w z; linarith [(hw01 z).2])
        ((integrable_const _).sub hwi)).1 h0
      filter_upwards [this] with z hz
      have h' : (1:ℝ) - w z = 0 := hz
      linarith
    refine le_of_eq (integral_congr_ae ?_)
    filter_upwards [hz] with z hz; simp [hz]
  · set a := quantile μ (1 - s) with ha
    have hpt : ∀ z, 0 ≤ (topSelector μ s z - w z) * (f z - f a) := by
      intro z
      unfold topSelector
      rw [if_neg (not_le.2 hs.1), if_neg (not_le.2 h1)]
      rcases lt_trichotomy z a with h | h | h
      · rw [if_neg (not_lt.2 h.le), if_neg h.ne]
        have := hf h.le
        nlinarith [(hw01 z).1]
      · subst h; simp
      · rw [if_pos h]
        have := hf h.le
        nlinarith [(hw01 z).2]
    have h1' : 0 ≤ ∫ z, (topSelector μ s z - w z) * (f z - f a) ∂μ :=
      integral_nonneg hpt
    have e : ∀ z, (topSelector μ s z - w z) * (f z - f a) =
        (topSelector μ s z * f z - w z * f z) - f a * (topSelector μ s z - w z) := fun z => by ring
    simp_rw [e] at h1'
    have i1 : Integrable (fun z => topSelector μ s z * f z - w z * f z) μ := hTf.sub hwf
    have i2 : Integrable (fun z => f a * (topSelector μ s z - w z)) μ :=
      (hTi.sub hwi).const_mul _
    rw [integral_sub i1 i2, integral_sub hTf hwf,
      integral_const_mul, integral_sub hTi hwi, hTint, hmass] at h1'
    linarith


theorem nbhd_of_cont (hμ : Integrable id μ) {c : ℝ} (hc : c ∈ Ioc (0:ℝ) 1) (P : ℝ → Prop)
    (hP : ∀ᶠ s in 𝓝[Ioc (0:ℝ) 1] c, P s) :
    ∃ δ > 0, ∀ s ∈ Ioc (0:ℝ) 1, |s - c| < δ → P s := by
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hP
  obtain ⟨δ, hδ, h⟩ := hP
  exact ⟨δ, hδ, fun s hs hd => h (by simpa [Real.dist_eq] using hd) hs⟩

theorem capacity_spec' (hμ : Integrable id μ) (h : ℝ) (hne : (capacitySet μ h).Nonempty) :
    capacity μ h ∈ capacitySet μ h ∧ (capacity μ h < 1 → poolMean μ (capacity μ h) = h) := by
  have hbdd : BddAbove (capacitySet μ h) := ⟨1, fun s hs => hs.2.1⟩
  have hcap : capacity μ h = sSup (capacitySet μ h) := by unfold capacity; rw [if_pos hne]
  rw [hcap]
  set c := sSup (capacitySet μ h) with hcdef
  obtain ⟨s0, hs0⟩ := hne
  have hc0 : 0 < c := lt_of_lt_of_le hs0.1 (le_csSup hbdd hs0)
  have hc1 : c ≤ 1 := csSup_le ⟨s0, hs0⟩ fun s hs => hs.2.1
  have hcI : c ∈ Ioc (0:ℝ) 1 := ⟨hc0, hc1⟩
  have hcont : ContinuousWithinAt (poolMean μ) (Ioc (0:ℝ) 1) c :=
    poolMean_continuousOn' μ hμ c hcI
  have hanti := poolMean_antitoneOn' μ hμ
  have hge : h ≤ poolMean μ c := by
    by_contra hlt
    push Not at hlt
    obtain ⟨δ, hδ, hP⟩ := nbhd_of_cont μ hμ hcI (fun s => poolMean μ s < h)
      (hcont.eventually (eventually_lt_nhds hlt))
    obtain ⟨s, hs, hlt2⟩ := exists_lt_of_lt_csSup ⟨s0, hs0⟩ (show c - δ < c by linarith)
    have hsc : s ≤ c := le_csSup hbdd hs
    have := hP s ⟨hs.1, hs.2.1⟩ (by rw [abs_lt]; constructor <;> linarith)
    linarith [hs.2.2]
  refine ⟨⟨hc0, hc1, hge⟩, fun hc => ?_⟩
  by_contra hne'
  have hgt : h < poolMean μ c := lt_of_le_of_ne hge (Ne.symm hne')
  obtain ⟨δ, hδ, hP⟩ := nbhd_of_cont μ hμ hcI (fun s => h < poolMean μ s)
    (hcont.eventually (eventually_gt_nhds hgt))
  set s := min (c + δ / 2) 1 with hsdef
  have hs1 : c < s := lt_min (by linarith) hc
  have hsI : s ∈ Ioc (0:ℝ) 1 := ⟨by linarith, min_le_right _ _⟩
  have := hP s hsI (by
    rw [abs_lt]; constructor <;> linarith [min_le_left (c + δ / 2) 1])
  have hsS : s ∈ capacitySet μ h := ⟨hsI.1, hsI.2, this.le⟩
  exact absurd (le_csSup hbdd hsS) (not_le.2 hs1)

end PersuasionByParts.Known.Dev.Pool

/-! ### Interface statements -/

namespace PersuasionByParts.Known.Iface
open PersuasionByParts.Known.Dev.Pool

theorem poolMean_antitoneOn (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ) :
    AntitoneOn (poolMean μ) (Ioc 0 1) := poolMean_antitoneOn' μ hμ

/-- Hardy–Littlewood / bathtub: among selectors `w : ℝ → [0,1]` of the same mass `s`, the top
selector maximises `∫ w f` for a nondecreasing `f`. -/
theorem selector_le_topSelector (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    {w : ℝ → ℝ} (hw : Measurable w) (hw01 : ∀ z, w z ∈ Icc 0 1)
    {s : ℝ} (hs : s ∈ Ioc 0 1) (hmass : ∫ z, w z ∂μ = s)
    {f : ℝ → ℝ} (hf : Monotone f) (hfi : Integrable f μ) :
    ∫ z, w z * f z ∂μ ≤ ∫ z, topSelector μ s z * f z ∂μ :=
  bathtub μ hμ hw hw01 hs hmass hf hfi

/-- the capacity is attained, and equals the point where the pool mean crosses the target. -/
theorem capacity_spec (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ) (h : ℝ)
    (hne : (capacitySet μ h).Nonempty) :
    capacity μ h ∈ capacitySet μ h ∧ (capacity μ h < 1 → poolMean μ (capacity μ h) = h) :=
  capacity_spec' μ hμ h hne

theorem capacity_eq_zero (μ : Measure ℝ) (h : ℝ) (hne : ¬ (capacitySet μ h).Nonempty) :
    capacity μ h = 0 := by
  unfold capacity; simp [hne]

theorem capacity_nonneg_le_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    (h : ℝ) : 0 ≤ capacity μ h ∧ capacity μ h ≤ 1 := by
  by_cases hne : (capacitySet μ h).Nonempty
  · have := (capacity_spec μ hμ h hne).1
    exact ⟨this.1.le, this.2.1⟩
  · rw [capacity_eq_zero μ h hne]; norm_num

/-- every `s ∈ (0,1]` with `h ≤ poolMean μ s` is at most the capacity -/
theorem le_capacity (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ) {h s : ℝ}
    (hs : s ∈ capacitySet μ h) : s ≤ capacity μ h := by
  have hbdd : BddAbove (capacitySet μ h) := ⟨1, fun s hs => hs.2.1⟩
  unfold capacity
  rw [if_pos ⟨s, hs⟩]
  exact le_csSup hbdd hs

end PersuasionByParts.Known.Iface
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
noncomputable section

namespace PersuasionByParts.Known.Dev.Post

variable {Ω 𝓧 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝓧] [StandardBorelSpace Ω]
  [Nonempty Ω] (κ : Kernel Ω 𝓧) [IsMarkovKernel κ] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- the signal law of a set is the integral of the kernel mass -/
theorem real_comp_apply {B : Set 𝓧} (hB : MeasurableSet B) :
    (κ ∘ₘ μ).real B = ∫ x, (κ x).real B ∂μ := by
  rw [measureReal_def, Measure.bind_apply hB κ.aemeasurable]
  simp only [measureReal_def]
  rw [integral_toReal (κ.measurable_coe hB).aemeasurable
    (Eventually.of_forall fun x => measure_lt_top _ _)]

/-- integrability of the joint test function `1_B(s) f(x)` against the posterior-joint law -/
private theorem integrable_joint (f : Ω → ℝ) (hfm : Measurable f) (hf : Integrable f μ)
    {B : Set 𝓧} (hB : MeasurableSet B) :
    Integrable (fun p : 𝓧 × Ω => B.indicator (fun _ => (1:ℝ)) p.1 * f p.2)
      ((κ ∘ₘ μ) ⊗ₘ κ†μ) := by
  rw [compProd_posterior_eq_map_swap]
  have hm : Measurable (fun p : 𝓧 × Ω => B.indicator (fun _ => (1:ℝ)) p.1 * f p.2) :=
    ((measurable_const.indicator hB).comp measurable_fst).mul (hfm.comp measurable_snd)
  rw [integrable_map_measure hm.aestronglyMeasurable measurable_swap.aemeasurable]
  have h1 : Integrable (fun p : Ω × 𝓧 => f p.1) (μ ⊗ₘ κ) := by
    have hmap : (μ ⊗ₘ κ).map Prod.fst = μ := Measure.fst_compProd μ κ
    have h0 : Integrable f ((μ ⊗ₘ κ).map Prod.fst) := by rw [hmap]; exact hf
    exact (integrable_map_measure (by rw [hmap]; exact hfm.aestronglyMeasurable)
      measurable_fst.aemeasurable).1 h0
  refine h1.norm.mono' ?_ (Eventually.of_forall fun p => ?_)
  · exact (hm.comp measurable_swap).aestronglyMeasurable
  · simp only [Function.comp, Prod.fst_swap, Prod.snd_swap, Real.norm_eq_abs, abs_mul]
    by_cases h : p.2 ∈ B <;> simp [h, Real.norm_eq_abs]

/-- Main identity: `∫_B E[f | S = s] d(law S) = E[f(X) · 1{S ∈ B}]`. -/
theorem setIntegral_posterior (f : Ω → ℝ) (hfm : Measurable f) (hf : Integrable f μ)
    {B : Set 𝓧} (hB : MeasurableSet B) :
    ∫ s in B, ∫ x, f x ∂(κ†μ) s ∂(κ ∘ₘ μ) = ∫ x, f x * (κ x).real B ∂μ := by
  have hint := integrable_joint κ μ f hfm hf hB
  have h1 : ∫ p, B.indicator (fun _ => (1:ℝ)) p.1 * f p.2 ∂((κ ∘ₘ μ) ⊗ₘ κ†μ) =
      ∫ s in B, ∫ x, f x ∂(κ†μ) s ∂(κ ∘ₘ μ) := by
    rw [Measure.integral_compProd hint, ← integral_indicator hB]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    simp only
    by_cases h : s ∈ B <;> simp [h]
  rw [← h1, compProd_posterior_eq_map_swap]
  have hm : Measurable (fun p : 𝓧 × Ω => B.indicator (fun _ => (1:ℝ)) p.1 * f p.2) :=
    ((measurable_const.indicator hB).comp measurable_fst).mul (hfm.comp measurable_snd)
  rw [integral_map measurable_swap.aemeasurable hm.aestronglyMeasurable]
  simp only [Prod.fst_swap, Prod.snd_swap]
  have hint2 : Integrable (fun p : Ω × 𝓧 => B.indicator (fun _ => (1:ℝ)) p.2 * f p.1) (μ ⊗ₘ κ) := by
    have := hint
    rw [compProd_posterior_eq_map_swap,
      integrable_map_measure hm.aestronglyMeasurable measurable_swap.aemeasurable] at this
    exact this
  rw [Measure.integral_compProd hint2]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  have : ∀ y, B.indicator (fun _ => (1:ℝ)) y * f x = f x * B.indicator (fun _ => (1:ℝ)) y :=
    fun y => mul_comm _ _
  simp_rw [this, integral_const_mul, integral_indicator_const _ hB]
  simp [measureReal_def]

theorem integrable_posterior_integral (f : Ω → ℝ) (hfm : Measurable f) (hf : Integrable f μ) :
    Integrable (fun s => ∫ x, f x ∂(κ†μ) s) (κ ∘ₘ μ) := by
  have h := integrable_joint κ μ f hfm hf (B := Set.univ) MeasurableSet.univ
  simp only [indicator_univ] at h
  have h2 := h.integral_compProd
  simpa [one_mul] using h2

/-- At a measurable atom of positive mass the posterior integral is pinned down. -/
theorem posterior_integral_atom (f : Ω → ℝ) (hfm : Measurable f) (hf : Integrable f μ)
    [MeasurableSingletonClass 𝓧] (σ : 𝓧) :
    (κ ∘ₘ μ).real {σ} * ∫ x, f x ∂(κ†μ) σ = ∫ x, f x * (κ x).real {σ} ∂μ := by
  have := setIntegral_posterior κ μ f hfm hf (measurableSet_singleton σ)
  rw [integral_singleton] at this
  simpa using this

end PersuasionByParts.Known.Dev.Post
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
noncomputable section

namespace PersuasionByParts.Known.Dev.PS
open PersuasionByParts.Known

theorem msc : MeasurableSingletonClass (Unit ⊕ ℝ) := by
  refine ⟨fun t => ?_⟩
  rcases t with u | r
  · have : ({Sum.inl u} : Set (Unit ⊕ ℝ)) = Sum.inl '' {u} := by simp
    rw [this]; exact (measurableSet_singleton _).inl_image
  · have : ({Sum.inr r} : Set (Unit ⊕ ℝ)) = Sum.inr '' {r} := by simp
    rw [this]; exact (measurableSet_singleton _).inr_image

theorem poolKernel_inl (μ : Measure ℝ) (s x : ℝ) (htop : topSelector μ s x ∈ Icc (0:ℝ) 1) :
    poolKernel μ s x {Sum.inl ()} = ENNReal.ofReal (topSelector μ s x) := by
  haveI := msc
  have hmeas : MeasurableSet (poolReport μ s ⁻¹' {Sum.inl ()}) :=
    measurable_poolReport μ s (measurableSet_singleton _)
  unfold poolKernel
  rw [Kernel.deterministic_comp_eq_map, Kernel.map_apply' _ (measurable_poolReport μ s) _ (measurableSet_singleton _),
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_apply measurable_prodMk_left hmeas]
  have : (Prod.mk x ⁻¹' (poolReport μ s ⁻¹' {Sum.inl ()})) = Iio (topSelector μ s x) := by
    ext u; simp [poolReport]
  rw [this]
  unfold privateUniform
  rw [Measure.restrict_apply measurableSet_Iio]
  have h2 : Iio (topSelector μ s x) ∩ Icc (0:ℝ) 1 = Ico 0 (topSelector μ s x) := by
    ext u
    simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_Ico]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩; exact ⟨h1, h2, by linarith [htop.2]⟩
  rw [h2, Real.volume_Ico]; simp

end PersuasionByParts.Known.Dev.PS

namespace PersuasionByParts.Known

end PersuasionByParts.Known
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
noncomputable section

namespace PersuasionByParts.Known.Dev.JC
open PersuasionByParts.Known

section avg
variable {X : Type*} [MeasurableSpace X] (ρ : Measure X) [IsProbabilityMeasure ρ]
  {T : X → ℝ} (hT : Measurable T)

include hT in
/-- averaging a selector along `T` and applying the bathtub inequality on the line -/
theorem avg_bound (hμ : Integrable id (ρ.map T)) {w : X → ℝ} (hw : Measurable w)
    (hw01 : ∀ x, w x ∈ Icc (0:ℝ) 1) {s : ℝ} (hs : 0 < s) (hmass : ∫ x, w x ∂ρ = s) :
    ∫ x, T x * w x ∂ρ ≤ s * poolMean (ρ.map T) s := by
  haveI : IsProbabilityMeasure (ρ.map T) := Measure.isProbabilityMeasure_map hT.aemeasurable
  set μ := ρ.map T with hμdef
  set ν := (ρ.withDensity (fun x => ENNReal.ofReal (w x))).map T with hνdef
  have hwle : ∀ x, ENNReal.ofReal (w x) ≤ 1 := fun x => by
    rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (hw01 x).2
  have hνle : ν ≤ μ := by
    refine Measure.le_iff.2 fun A hA => ?_
    rw [hνdef, hμdef, Measure.map_apply hT hA, Measure.map_apply hT hA,
      withDensity_apply _ (hT hA)]
    calc ∫⁻ x in T ⁻¹' A, ENNReal.ofReal (w x) ∂ρ ≤ ∫⁻ x in T ⁻¹' A, 1 ∂ρ :=
          lintegral_mono hwle
      _ = ρ (T ⁻¹' A) := by simp
  haveI : IsFiniteMeasure ν := isFiniteMeasure_of_le μ hνle
  have hac : ν ≪ μ := Measure.absolutelyContinuous_of_le hνle
  have hwi : Integrable w ρ := Integrable.of_bound hw.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_le]; exact ⟨by linarith [(hw01 x).1], (hw01 x).2⟩)
  have hνuniv : ν.real univ = s := by
    rw [hνdef, measureReal_def, Measure.map_apply hT MeasurableSet.univ, preimage_univ,
      withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hwi (Filter.Eventually.of_forall fun x => (hw01 x).1),
      hmass, ENNReal.toReal_ofReal hs.le]
  set wb : ℝ → ℝ := fun z => min 1 ((ν.rnDeriv μ z).toReal) with hwb
  have hwbm : Measurable wb :=
    measurable_const.min (Measure.measurable_rnDeriv ν μ).ennreal_toReal
  have hwb01 : ∀ z, wb z ∈ Icc (0:ℝ) 1 := fun z =>
    ⟨le_min zero_le_one ENNReal.toReal_nonneg, min_le_left _ _⟩
  have hae : ∀ᵐ z ∂μ, wb z = (ν.rnDeriv μ z).toReal := by
    filter_upwards [Measure.rnDeriv_le_one_of_le hνle] with z hz
    have : (ν.rnDeriv μ z).toReal ≤ 1 := by
      have := ENNReal.toReal_mono ENNReal.one_ne_top hz
      simpa using this
    exact min_eq_right this
  have hmass2 : ∫ z, wb z ∂μ = s := by
    rw [integral_congr_ae hae, Measure.integral_toReal_rnDeriv hac, hνuniv]
  have hs1 : s ≤ 1 := by
    rw [← hmass]
    calc ∫ x, w x ∂ρ ≤ ∫ x, (1:ℝ) ∂ρ := integral_mono hwi (integrable_const _)
          fun x => (hw01 x).2
      _ = 1 := by simp
  have hbath := PersuasionByParts.Known.Iface.selector_le_topSelector μ hμ hwbm hwb01
    ⟨hs, hs1⟩ hmass2 (f := id) monotone_id hμ
  have hmom : ∫ z, topSelector μ s z * id z ∂μ = s * poolMean μ s :=
    (Dev.Pool.top_spec μ hμ ⟨hs.le, hs1⟩).2.2
  have hI : ∫ z, wb z * id z ∂μ = ∫ x, T x * w x ∂ρ := by
    have h1 : ∫ z, wb z * id z ∂μ = ∫ z, (ν.rnDeriv μ z).toReal * id z ∂μ :=
      integral_congr_ae (by filter_upwards [hae] with z hz; rw [hz])
    rw [h1, integral_toReal_rnDeriv_mul hac, hνdef,
      integral_map hT.aemeasurable (by
        rw [← hνdef]; exact (measurable_id.aestronglyMeasurable))]
    rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [ENNReal.toReal_ofReal (hw01 x).1, mul_comm]
  rw [← hI]; linarith

end avg


section prior
variable {n : ℕ} (P : Prior n)

theorem total_meas : Measurable (total : (Fin n → ℝ) → ℝ) := by
  unfold total; fun_prop

instance : IsProbabilityMeasure (sumLaw P) :=
  Measure.isProbabilityMeasure_map (total_meas).aemeasurable

theorem integrable_total : Integrable (total : (Fin n → ℝ) → ℝ) (priorLaw P) := by
  have : (total : (Fin n → ℝ) → ℝ) = fun x => ∑ i, x i := rfl
  rw [this]
  refine integrable_finsetSum _ fun i _ => ?_
  have h0 : Integrable id ((priorLaw P).map (Function.eval i)) := by
    rw [priorLaw, (measurePreserving_eval P.marginal i).map_eq]; exact P.finiteMean i
  exact (integrable_map_measure aestronglyMeasurable_id (measurable_pi_apply i).aemeasurable).1 h0

theorem integrable_sumLaw : Integrable id (sumLaw P) :=
  (integrable_map_measure aestronglyMeasurable_id (total_meas).aemeasurable).2 (integrable_total P)

variable (E : JointExperiment n)

instance instProbSig : IsProbabilityMeasure (jointSignalLaw P E) := by
  unfold jointSignalLaw; infer_instance

theorem post_meas : Measurable (jointPosterior P E) :=
  ((total_meas (n := n)).stronglyMeasurable.integral_kernel).measurable

theorem payoff_eq (t : ℝ) :
    jointPayoff P E (cutoff t) = (jointSignalLaw P E).real {y | t ≤ jointPosterior P E y} := by
  have hB : MeasurableSet {y | t ≤ jointPosterior P E y} :=
    measurableSet_le measurable_const (post_meas P E)
  unfold jointPayoff
  have : (fun y => cutoff t (jointPosterior P E y)) =
      ({y | t ≤ jointPosterior P E y} : Set E.Signal).indicator (fun _ => (1:ℝ)) := by
    funext y; simp [cutoff, Set.indicator_apply]
  rw [this, integral_indicator_const _ hB]; simp


theorem payoff_nonneg (t : ℝ) : 0 ≤ jointPayoff P E (cutoff t) := by
  rw [payoff_eq]; exact measureReal_nonneg

theorem payoff_le_one (t : ℝ) : jointPayoff P E (cutoff t) ≤ 1 := by
  rw [payoff_eq]; exact measureReal_le_one

/-- the key upper bound: a positive acting mass `s` forces `t ≤ poolMean s`. -/
theorem acting_mass_spec (t : ℝ) (hpos : 0 < jointPayoff P E (cutoff t)) :
    jointPayoff P E (cutoff t) ∈ capacitySet (sumLaw P) t := by
  set B : Set E.Signal := {y | t ≤ jointPosterior P E y} with hBdef
  have hB : MeasurableSet B := measurableSet_le measurable_const (post_meas P E)
  set s := jointPayoff P E (cutoff t) with hsdef
  have hsB : s = (jointSignalLaw P E).real B := payoff_eq P E t
  refine ⟨hpos, payoff_le_one P E t, ?_⟩
  have hpost := Post.setIntegral_posterior E.kernel (priorLaw P) total (total_meas)
    (integrable_total P) hB
  have hint := Post.integrable_posterior_integral E.kernel (priorLaw P) total (total_meas)
    (integrable_total P)
  have h1 : t * s ≤ ∫ x, total x * (E.kernel x).real B ∂(priorLaw P) := by
    rw [← hpost]
    have : ∫ y in B, t ∂(jointSignalLaw P E) = t * s := by
      rw [setIntegral_const, hsB]; simp [mul_comm]
    rw [← this]
    exact setIntegral_mono_on (integrableOn_const (by simp) (by simp)) hint.integrableOn hB
      (fun y hy => hy)
  have hwm : Measurable (fun x => (E.kernel x).real B) :=
    (E.kernel.measurable_coe hB).ennreal_toReal
  have hw01 : ∀ x, (E.kernel x).real B ∈ Icc (0:ℝ) 1 := fun x =>
    ⟨measureReal_nonneg, measureReal_le_one⟩
  have hmass : ∫ x, (E.kernel x).real B ∂(priorLaw P) = s := by
    rw [hsB]; exact (Post.real_comp_apply E.kernel (priorLaw P) hB).symm
  have h2 := avg_bound (priorLaw P) (total_meas) (integrable_sumLaw P) hwm hw01 hpos hmass
  have : t * s ≤ s * poolMean (sumLaw P) s := le_trans h1 h2
  nlinarith


theorem pool_attains (t s0 : ℝ) (hs0 : s0 ∈ capacitySet (sumLaw P) t) :
    s0 ≤ jointPayoff P (jointPool P s0) (cutoff t) := by
  have msc0 : MeasurableSingletonClass (Unit ⊕ ℝ) := Dev.PS.msc
  have msc : MeasurableSingletonClass (jointPool P s0).Signal := Dev.PS.msc
  set μ := sumLaw P with hμdef
  have hs0I : s0 ∈ Icc (0:ℝ) 1 := ⟨hs0.1.le, hs0.2.1⟩
  obtain ⟨hmem, hint, hmom⟩ := Dev.Pool.top_spec μ (integrable_sumLaw P) hs0I
  have hmeas0 : MeasurableSet ({(Sum.inl () : Unit ⊕ ℝ)} : Set (Unit ⊕ ℝ)) :=
    measurableSet_singleton _
  have hmap : ∀ g : ℝ → ℝ, Measurable g → ∫ x, g (total x) ∂(priorLaw P) = ∫ z, g z ∂μ :=
    fun g hg => (integral_map (total_meas).aemeasurable hg.aestronglyMeasurable).symm
  have hker : ∀ x, ((jointPool P s0).kernel x).real ({Sum.inl ()} : Set (Unit ⊕ ℝ)) =
      topSelector μ s0 (total x) := fun x => by
    show ((poolKernel μ s0).comap total (total_meas) x).real ({Sum.inl ()} : Set (Unit ⊕ ℝ)) = _
    rw [Kernel.comap_apply, measureReal_def, Dev.PS.poolKernel_inl μ s0 _ (hmem _),
      ENNReal.toReal_ofReal (hmem _).1]
  have hmass : (jointSignalLaw P (jointPool P s0)).real ({Sum.inl ()} : Set (Unit ⊕ ℝ)) = s0 := by
    have := Post.real_comp_apply (jointPool P s0).kernel (priorLaw P) hmeas0
    unfold jointSignalLaw
    rw [this]
    simp_rw [hker]
    rw [hmap _ (measurable_topSelector μ s0), hint]
  have hat := Post.posterior_integral_atom (jointPool P s0).kernel (priorLaw P) total
    (total_meas) (integrable_total P) (Sum.inl ())
  have hrhs : ∫ x, total x * ((jointPool P s0).kernel x).real
        ({(Sum.inl () : (jointPool P s0).Signal)} : Set (jointPool P s0).Signal) ∂(priorLaw P) =
      ∫ x, (fun z => topSelector μ s0 z * z) (total x) ∂(priorLaw P) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by
      show total x * ((jointPool P s0).kernel x).real ({Sum.inl ()} : Set (Unit ⊕ ℝ)) = _
      rw [hker x, mul_comm])
  have h1 := hat.trans hrhs
  rw [hmap (fun z => topSelector μ s0 z * z)
    ((measurable_topSelector μ s0).mul measurable_id), hmom] at h1
  have hmass' : ((jointPool P s0).kernel ∘ₘ priorLaw P).real
      ({(Sum.inl () : (jointPool P s0).Signal)} : Set (jointPool P s0).Signal) = s0 := hmass
  have h2 := (congrArg (fun r => r * jointPosterior P (jointPool P s0) (Sum.inl ())) hmass').symm.trans h1
  have hpm : jointPosterior P (jointPool P s0) (Sum.inl ()) = poolMean μ s0 :=
    mul_left_cancel₀ hs0.1.ne' h2
  have hin : (Sum.inl () : Unit ⊕ ℝ) ∈
      {y : (jointPool P s0).Signal | t ≤ jointPosterior P (jointPool P s0) y} := by
    show t ≤ jointPosterior P (jointPool P s0) (Sum.inl ())
    rw [hpm]; exact hs0.2.2
  have hle := measureReal_mono (μ := jointSignalLaw P (jointPool P s0)) (singleton_subset_iff.2 hin)
    (measure_ne_top (jointSignalLaw P (jointPool P s0)) _)
  rw [payoff_eq]
  exact hmass.symm.le.trans hle


theorem payoff_le_capacity (t : ℝ) : jointPayoff P E (cutoff t) ≤ capacity (sumLaw P) t := by
  rcases (payoff_nonneg P E t).eq_or_lt with h | h
  · rw [← h]; exact (Iface.capacity_nonneg_le_one (sumLaw P) (integrable_sumLaw P) t).1
  · exact Iface.le_capacity (sumLaw P) (integrable_sumLaw P) (acting_mass_spec P E t h)

end prior

end PersuasionByParts.Known.Dev.JC

namespace PersuasionByParts.Known

/-- Lemma 1.3, printed p. 3 / PDF p. 4: maximum, its actual top-pool attainment,
and both directions of the characterization, including an empty capacity set. -/
theorem chk_joint_cutoff_value {n : ℕ} (P : Prior n) (hn : 0 < n) (t : ℝ) :
    jointCutoff P t = capacity (sumLaw P) t ∧
    ((capacitySet (sumLaw P) t).Nonempty →
      IsGreatest (capacitySet (sumLaw P) t) (jointCutoff P t)) ∧
    jointPayoff P (jointPool P (jointCutoff P t)) (cutoff t) = jointCutoff P t ∧
    (∀ q : ℝ, q ∈ Ioc 0 1 →
      (q ≤ jointCutoff P t ↔ t ≤ poolMean (sumLaw P) q)) := by
  have hμ := Dev.JC.integrable_sumLaw P
  haveI := Dev.JC.instProbSig P
  set c := capacity (sumLaw P) t with hc
  have hub : ∀ E : JointExperiment n, jointPayoff P E (cutoff t) ≤ c :=
    fun E => Dev.JC.payoff_le_capacity P E t
  have hlow : ∀ E : JointExperiment n, ¬ (capacitySet (sumLaw P) t).Nonempty →
      jointPayoff P E (cutoff t) = c := fun E hne => by
    have h0 : c = 0 := Iface.capacity_eq_zero (sumLaw P) t hne
    exact le_antisymm (hub E) (h0 ▸ Dev.JC.payoff_nonneg P E t)
  have hatt : (capacitySet (sumLaw P) t).Nonempty →
      jointPayoff P (jointPool P c) (cutoff t) = c := fun hne =>
    le_antisymm (hub _) (Dev.JC.pool_attains P t c (Iface.capacity_spec (sumLaw P) hμ t hne).1)
  have hmax : IsGreatest (jointPayoffs P (cutoff t)) c := by
    refine ⟨?_, ?_⟩
    · by_cases hne : (capacitySet (sumLaw P) t).Nonempty
      · exact ⟨jointPool P c, (hatt hne).symm⟩
      · exact ⟨jointRevelation n, (hlow _ hne).symm⟩
    · rintro v ⟨E, rfl⟩; exact hub E
  have hcut : jointCutoff P t = c := hmax.csSup_eq
  rw [hcut]
  refine ⟨rfl, fun hne => ?_, ?_, fun q hq => ?_⟩
  · exact ⟨(Iface.capacity_spec (sumLaw P) hμ t hne).1, fun q hq => Iface.le_capacity _ hμ hq⟩
  · by_cases hne : (capacitySet (sumLaw P) t).Nonempty
    · exact hatt hne
    · exact hlow _ hne
  · constructor
    · intro hqc
      have hne : (capacitySet (sumLaw P) t).Nonempty := by
        by_contra hne
        have h0 : c = 0 := Iface.capacity_eq_zero (sumLaw P) t hne
        linarith [hq.1]
      have hcs := (Iface.capacity_spec (sumLaw P) hμ t hne).1
      exact le_trans hcs.2.2 (Iface.poolMean_antitoneOn (sumLaw P) hμ ⟨hq.1, hq.2⟩
        ⟨hcs.1, hcs.2.1⟩ hqc)
    · intro hqt
      exact Iface.le_capacity _ hμ ⟨hq.1, hq.2, hqt⟩

end PersuasionByParts.Known
end
end

theorem solution : type_of% @PersuasionByParts.Known.chk_joint_cutoff_value := @PersuasionByParts.Known.chk_joint_cutoff_value
