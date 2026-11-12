-- Prove2me | solution 1 for PersuasionByParts.Known.capacity_lemma
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T16:55:05.521444+00:00
-- url     : https://prove2.me/submissions/a2c8b6ad-9b9a-4029-9946-f3db10031b59

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

theorem Q_le_poolMean (hμ : Integrable id μ) {s : ℝ} (hs : s ∈ Ioo (0:ℝ) 1) :
    quantile μ (1 - s) ≤ poolMean μ s := by
  rw [G_eq, le_div_iff₀ hs.1]
  linarith [mul_Q_le_G μ hμ hs]

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


theorem top_eq_one_of_gt (hμ : Integrable id μ) {s : ℝ} (hs : s ∈ Ioc (0:ℝ) 1) {z : ℝ}
    (hz : poolMean μ s < z) : topSelector μ s z = 1 := by
  rcases hs.2.eq_or_lt with rfl | h1
  · simp [topSelector]
  · have := Q_le_poolMean μ hμ ⟨hs.1, h1⟩
    unfold topSelector
    rw [if_neg (not_le.2 hs.1), if_neg (not_le.2 h1), if_pos (lt_of_le_of_lt this hz)]

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

/-- a value strictly above the pool mean is selected fully -/
theorem topSelector_eq_one_of_gt (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    {s : ℝ} (hs : s ∈ Ioc 0 1) {z : ℝ} (hz : poolMean μ s < z) : topSelector μ s z = 1 :=
  top_eq_one_of_gt μ hμ hs hz

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

end PersuasionByParts.Known.Dev.Post
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
noncomputable section

/-! Three facts about the top selector of one probability measure, NOT in `Iface.lean`, but
available in `Pool.lean` (`top_mem`, `top_spec`). -/

namespace PersuasionByParts.Known.Dev.CapExtra
open PersuasionByParts.Known

theorem topSelector_mem_Icc (μ : Measure ℝ) [IsProbabilityMeasure μ] {s : ℝ} (hs : s ∈ Ioc 0 1)
    (z : ℝ) : topSelector μ s z ∈ Icc (0:ℝ) 1 := by
  rcases hs.2.eq_or_lt with h1 | h1
  · subst h1
    simp [topSelector]
    norm_num
  · exact Dev.Pool.top_mem μ ⟨hs.1, h1⟩ z

theorem integral_topSelector (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    {s : ℝ} (hs : s ∈ Ioc 0 1) : ∫ z, topSelector μ s z ∂μ = s :=
  (Dev.Pool.top_spec μ hμ ⟨hs.1.le, hs.2⟩).2.1

theorem integral_topSelector_mul (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ)
    {s : ℝ} (hs : s ∈ Ioc 0 1) : ∫ z, topSelector μ s z * z ∂μ = s * poolMean μ s :=
  (Dev.Pool.top_spec μ hμ ⟨hs.1.le, hs.2⟩).2.2

end PersuasionByParts.Known.Dev.CapExtra
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
noncomputable section

namespace PersuasionByParts.Known.Dev.Cap
open PersuasionByParts.Known

/-- `P`-quantile Galois property (copied from the pooling files so this module is stable). -/
theorem quantile_ge_cdf (μ : Measure ℝ) [IsProbabilityMeasure μ] {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) :
    u ≤ cdf μ (quantile μ u) := by
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
    have hcont : ContinuousWithinAt (cdf μ) (Ioi a) a :=
      ((cdf μ).right_continuous a).mono Ioi_subset_Ici_self
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
  have hq : quantile μ u = a := by
    unfold quantile PersuasionNetworks.stateQuantile
    have hgal : ∀ t, u ≤ cdf μ t ↔ a ≤ t := fun t =>
      ⟨fun h => csInf_le hbdd h, fun h => le_trans haS (hmono h)⟩
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
  rw [hq]; exact haS

/-- the mass strictly above the quantile is at most `1 - u`. -/
theorem measureReal_Ioi_quantile_le (μ : Measure ℝ) [IsProbabilityMeasure μ] {u : ℝ}
    (hu : u ∈ Ioo (0:ℝ) 1) : μ.real (Ioi (quantile μ u)) ≤ 1 - u := by
  have h1 := quantile_ge_cdf μ hu
  rw [cdf_eq_real] at h1
  have : μ.real (Ioi (quantile μ u)) = 1 - μ.real (Iic (quantile μ u)) := by
    rw [← compl_Iic, measureReal_compl measurableSet_Iic]; simp
  linarith

variable {n : ℕ} (P : Prior n)

/-- `U = E[(X - t)^+]`. -/
def Uex (t : ℝ) : ℝ := ∫ x, max (total x - t) 0 ∂priorLaw P

/-- the top-`q` selection weight of the sum. -/
def Wsel (q : ℝ) (x : Fin n → ℝ) : ℝ := topSelector (sumLaw P) q (total x)

theorem measurable_total : Measurable (total : (Fin n → ℝ) → ℝ) := by
  unfold total; fun_prop

theorem measurable_others (i : Fin n) : Measurable (others i : (Fin n → ℝ) → ℝ) := by
  unfold others; fun_prop

theorem integrable_coord (i : Fin n) : Integrable (fun x : Fin n → ℝ => x i) (priorLaw P) := by
  have h := (P.finiteMean i)
  rw [← (measurePreserving_eval P.marginal i).map_eq] at h
  have := (integrable_map_measure (μ := Measure.pi P.marginal) (f := Function.eval i)
    (g := (id : ℝ → ℝ)) measurable_id.aestronglyMeasurable
    (measurable_pi_apply i).aemeasurable).1 h
  simpa [priorLaw] using this

theorem integrable_total : Integrable (total : (Fin n → ℝ) → ℝ) (priorLaw P) := by
  unfold total
  exact integrable_finsetSum _ fun i _ => integrable_coord P i

instance : IsProbabilityMeasure (sumLaw P) := by
  unfold sumLaw
  exact Measure.isProbabilityMeasure_map measurable_total.aemeasurable

instance (i : Fin n) : IsProbabilityMeasure (othersLaw P i) := by
  unfold othersLaw
  exact Measure.isProbabilityMeasure_map (measurable_others i).aemeasurable

theorem integrable_id_sumLaw : Integrable id (sumLaw P) := by
  unfold sumLaw
  exact (integrable_map_measure measurable_id.aestronglyMeasurable
    measurable_total.aemeasurable).2 (integrable_total P)

theorem integrable_pos (t : ℝ) : Integrable (fun x => max (total x - t) 0) (priorLaw P) :=
  ((integrable_total P).sub (integrable_const t)).pos_part

theorem Uex_nonneg (t : ℝ) : 0 ≤ Uex P t :=
  integral_nonneg fun _ => le_max_right _ _

theorem measurable_Wsel (q : ℝ) : Measurable (Wsel P q) :=
  (measurable_topSelector _ _).comp measurable_total

theorem Wsel_mem (q : ℝ) (hq : q ∈ Ioc 0 1) (x : Fin n → ℝ) : Wsel P q x ∈ Icc (0:ℝ) 1 :=
  CapExtra.topSelector_mem_Icc _ hq _

theorem integrable_Wsel_mul (q : ℝ) (hq : q ∈ Ioc 0 1) {g : (Fin n → ℝ) → ℝ}
    (hg : Integrable g (priorLaw P)) : Integrable (fun x => Wsel P q x * g x) (priorLaw P) :=
  hg.bdd_mul (c := 1) (measurable_Wsel P q).aestronglyMeasurable
    (Eventually.of_forall fun x => by
      have := Wsel_mem P q hq x
      rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2)

theorem integrable_Wsel (q : ℝ) (hq : q ∈ Ioc 0 1) : Integrable (Wsel P q) (priorLaw P) := by
  simpa using integrable_Wsel_mul P q hq (integrable_const (1:ℝ))

theorem integral_Wsel (q : ℝ) (hq : q ∈ Ioc 0 1) : ∫ x, Wsel P q x ∂priorLaw P = q := by
  have := integral_map (μ := priorLaw P) (φ := total)
    measurable_total.aemeasurable (f := topSelector (sumLaw P) q)
    (measurable_topSelector _ _).aestronglyMeasurable
  unfold Wsel
  rw [← this]
  exact CapExtra.integral_topSelector _ (integrable_id_sumLaw P) hq

theorem integral_Wsel_total (q : ℝ) (hq : q ∈ Ioc 0 1) :
    ∫ x, Wsel P q x * total x ∂priorLaw P = q * poolMean (sumLaw P) q := by
  have := integral_map (μ := priorLaw P) (φ := total)
    measurable_total.aemeasurable (f := fun z => topSelector (sumLaw P) q z * z)
    ((measurable_topSelector _ _).mul measurable_id).aestronglyMeasurable
  unfold Wsel
  rw [← this]
  exact CapExtra.integral_topSelector_mul _ (integrable_id_sumLaw P) hq

/-- (2.3): `E[W (t - X)^+] ≤ E[(X - t)^+] = U`. -/
theorem integral_Wsel_neg_le (q t : ℝ) (hq : q ∈ Ioc 0 1) (ht : t ≤ poolMean (sumLaw P) q) :
    ∫ x, Wsel P q x * max (t - total x) 0 ∂priorLaw P ≤ Uex P t := by
  have hi1 : Integrable (fun x => max (total x - t) 0) (priorLaw P) := integrable_pos P t
  have hi2 : Integrable (fun x => Wsel P q x * max (total x - t) 0) (priorLaw P) :=
    integrable_Wsel_mul P q hq hi1
  have hi3 : Integrable (fun x => Wsel P q x * (total x - t)) (priorLaw P) :=
    integrable_Wsel_mul P q hq ((integrable_total P).sub (integrable_const t))
  have hi4 : Integrable (fun x => Wsel P q x * max (t - total x) 0) (priorLaw P) :=
    integrable_Wsel_mul P q hq (((integrable_const t).sub (integrable_total P)).pos_part)
  have h0 : 0 ≤ ∫ x, Wsel P q x * (total x - t) ∂priorLaw P := by
    have e : ∫ x, Wsel P q x * (total x - t) ∂priorLaw P =
        ∫ x, Wsel P q x * total x ∂priorLaw P - t * ∫ x, Wsel P q x ∂priorLaw P := by
      rw [← integral_const_mul, ← integral_sub (integrable_Wsel_mul P q hq (integrable_total P))
        ((integrable_Wsel P q hq).const_mul t)]
      congr 1; ext x; ring
    rw [e, integral_Wsel_total P q hq, integral_Wsel P q hq]
    nlinarith [hq.1]
  have e2 : ∀ x, Wsel P q x * max (t - total x) 0 =
      Wsel P q x * max (total x - t) 0 - Wsel P q x * (total x - t) := by
    intro x
    rcases le_total (total x) t with h | h
    · rw [max_eq_right (by linarith : total x - t ≤ 0), max_eq_left (by linarith : (0:ℝ) ≤ t - total x)]
      ring
    · rw [max_eq_right (by linarith : t - total x ≤ 0), max_eq_left (by linarith : (0:ℝ) ≤ total x - t)]
      ring
  simp_rw [e2]
  rw [integral_sub hi2 hi3]
  have : ∫ x, Wsel P q x * max (total x - t) 0 ∂priorLaw P ≤ Uex P t := by
    unfold Uex
    refine integral_mono hi2 hi1 fun x => ?_
    have := Wsel_mem P q hq x
    have h2 : 0 ≤ max (total x - t) 0 := le_max_right _ _
    nlinarith [this.1, this.2]
  linarith

/-- the probability that the others exceed their `(1-q/3)`-quantile is at most `q/3`. -/
theorem others_tail (q t : ℝ) (hq : q ∈ Ioc 0 1) (i : Fin n) :
    (priorLaw P).real {x | t - target P q t i < others i x} ≤ q / 3 := by
  have hu : (1 - q / 3) ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hq.1, hq.2], by linarith [hq.1]⟩
  have h := measureReal_Ioi_quantile_le (othersLaw P i) hu
  have e : {x : Fin n → ℝ | t - target P q t i < others i x} =
      others i ⁻¹' Ioi (quantile (othersLaw P i) (1 - q / 3)) := by
    ext x; simp [target]
  rw [e]
  have : (priorLaw P).real (others i ⁻¹' Ioi (quantile (othersLaw P i) (1 - q / 3))) =
      (othersLaw P i).real (Ioi (quantile (othersLaw P i) (1 - q / 3))) := by
    unfold othersLaw
    rw [Measure.real, Measure.real, Measure.map_apply (measurable_others i) measurableSet_Ioi]
  rw [this]; linarith

theorem coordinateCapacity_nonneg (q t : ℝ) (i : Fin n) : 0 ≤ coordinateCapacity P q t i :=
  (Iface.capacity_nonneg_le_one (P.marginal i) (P.finiteMean i) _).1

end PersuasionByParts.Known.Dev.Cap
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
noncomputable section

namespace PersuasionByParts.Known.Dev.Cap
open PersuasionByParts.Known

variable {n : ℕ} (P : Prior n)

/-- Step 1: `U > 0`. -/
theorem Uex_pos (q t : ℝ) (hq : q ∈ Ioc 0 1) (ht : t ≤ poolMean (sumLaw P) q)
    (hp : revelationProbability P t < q / 3) : 0 < Uex P t := by
  by_contra hU
  have hU0 : Uex P t = 0 := le_antisymm (not_lt.1 hU) (Uex_nonneg P t)
  have hneg := integral_Wsel_neg_le P q t hq ht
  have hi4 : Integrable (fun x => Wsel P q x * max (t - total x) 0) (priorLaw P) :=
    integrable_Wsel_mul P q hq (((integrable_const t).sub (integrable_total P)).pos_part)
  have h0 : ∀ᵐ x ∂priorLaw P, Wsel P q x * max (t - total x) 0 = 0 := by
    have := (integral_eq_zero_iff_of_nonneg (fun x => mul_nonneg (Wsel_mem P q hq x).1
      (le_max_right _ _)) hi4).1 (le_antisymm (hU0 ▸ hneg)
      (integral_nonneg fun x => mul_nonneg (Wsel_mem P q hq x).1 (le_max_right _ _)))
    exact this
  have hbound : ∀ᵐ x ∂priorLaw P, Wsel P q x ≤ Set.indicator {x | t ≤ total x} (fun _ => (1:ℝ)) x := by
    filter_upwards [h0] with x hx
    by_cases hW : Wsel P q x = 0
    · rw [hW]; exact Set.indicator_nonneg (fun _ _ => zero_le_one) x
    · have hm : max (t - total x) 0 = 0 := by
        rcases mul_eq_zero.1 hx with h | h
        · exact absurd h hW
        · exact h
      have : t ≤ total x := by
        have := le_max_left (t - total x) 0
        linarith
      rw [Set.indicator_of_mem (show x ∈ {x | t ≤ total x} from this)]
      exact (Wsel_mem P q hq x).2
  have hint := integral_mono_ae (integrable_Wsel P q hq)
    ((integrable_const (1:ℝ)).indicator (measurableSet_le measurable_const measurable_total)) hbound
  have hind : ∫ x, Set.indicator {x | t ≤ total x} (fun _ => (1:ℝ)) x ∂priorLaw P =
      (priorLaw P).real {x | t ≤ total x} := by
    rw [integral_indicator (measurableSet_le measurable_const measurable_total)]; simp
  rw [integral_Wsel P q hq, hind] at hint
  have : revelationProbability P t = (priorLaw P).real {x | t ≤ total x} := rfl
  linarith [hq.1]

theorem integrable_min_coord (h : Fin n → ℝ) (i : Fin n) :
    Integrable (fun x : Fin n → ℝ => min (x i) (h i)) (priorLaw P) :=
  by
  have := (integrable_coord P i).sub (((integrable_coord P i).sub (integrable_const (h i))).pos_part)
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.sub_apply]
  rcases le_total (x i) (h i) with h1 | h1
  · rw [min_eq_left h1, max_eq_right (by linarith)]; ring
  · rw [min_eq_right h1, max_eq_left (by linarith)]; ring

theorem integrable_C (h : Fin n → ℝ) :
    Integrable (fun x : Fin n → ℝ => ∑ i, min (x i) (h i)) (priorLaw P) :=
  integrable_finsetSum _ fun i _ => integrable_min_coord P h i

theorem integral_marginal_pos (i : Fin n) (c : ℝ) :
    ∫ x, max (x - c) 0 ∂(P.marginal i) = ∫ x, max (x i - c) 0 ∂(priorLaw P) := by
  rw [← (measurePreserving_eval P.marginal i).map_eq]
  rw [integral_map (measurable_pi_apply i).aemeasurable (by fun_prop)]
  rfl

/-- Step 1: the decomposition (2.1). -/
theorem Uex_le (q t : ℝ) :
    Uex P t ≤ ∑ i, (∫ x, max (x - target P q t i) 0 ∂(P.marginal i)) +
      ∫ x, max (∑ i, min (x i) (target P q t i) - t) 0 ∂priorLaw P := by
  simp_rw [integral_marginal_pos]
  have hR : ∀ i, Integrable (fun x : Fin n → ℝ => max (x i - target P q t i) 0) (priorLaw P) :=
    fun i => ((integrable_coord P i).sub (integrable_const _)).pos_part
  have hC : Integrable (fun x : Fin n → ℝ => max (∑ i, min (x i) (target P q t i) - t) 0)
      (priorLaw P) := ((integrable_C P (target P q t)).sub (integrable_const t)).pos_part
  rw [← integral_finsetSum _ (fun i _ => hR i), ← integral_add (integrable_finsetSum _ fun i _ => hR i) hC]
  unfold Uex
  refine integral_mono (integrable_pos P t) ((integrable_finsetSum _ fun i _ => hR i).add hC)
    fun x => ?_
  have hdec : total x = ∑ i, min (x i) (target P q t i) + ∑ i, max (x i - target P q t i) 0 := by
    unfold total
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases le_total (x i) (target P q t i) with h | h
    · rw [min_eq_left h, max_eq_right (by linarith)]; ring
    · rw [min_eq_right h, max_eq_left (by linarith)]; ring
  have hR0 : 0 ≤ ∑ i, max (x i - target P q t i) 0 :=
    Finset.sum_nonneg fun i _ => le_max_right _ _
  show max (total x - t) 0 ≤ _
  rw [hdec]
  rcases le_total (∑ i, min (x i) (target P q t i) - t) 0 with h | h
  · rw [max_eq_right h]
    refine max_le (by linarith) (by positivity)
  · rw [max_eq_left h]
    refine max_le (by linarith) (by positivity)

end PersuasionByParts.Known.Dev.Cap
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
noncomputable section

namespace PersuasionByParts.Known.Dev.CapTail1
open PersuasionByParts.Known

variable (ν : Measure ℝ) [IsProbabilityMeasure ν]

theorem integrable_pos_sub (hν : Integrable id ν) (h : ℝ) :
    Integrable (fun a : ℝ => max (a - h) 0) ν :=
  ((hν.sub (integrable_const h)).pos_part)

theorem integrable_neg_sub (hν : Integrable id ν) (h : ℝ) :
    Integrable (fun a : ℝ => max (h - a) 0) ν :=
  (((integrable_const h).sub hν).pos_part)

theorem integrable_sel {w : ℝ → ℝ} (hw : Measurable w) (hw01 : ∀ a, w a ∈ Icc (0:ℝ) 1) :
    Integrable w ν :=
  (integrable_const (1:ℝ)).mono' hw.aestronglyMeasurable
    (Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hw01 a).1]; exact (hw01 a).2)

theorem integrable_sel_mul (hν : Integrable id ν) {w : ℝ → ℝ} (hw : Measurable w)
    (hw01 : ∀ a, w a ∈ Icc (0:ℝ) 1) {g : ℝ → ℝ} (hg : Integrable g ν) :
    Integrable (fun a => w a * g a) ν :=
  hg.bdd_mul (c := 1) hw.aestronglyMeasurable
    (Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hw01 a).1]; exact (hw01 a).2)

/-- capacity zero: no mass above the target. -/
theorem U_zero_of_capacity_zero (hν : Integrable id ν) (h : ℝ) (h0 : capacity ν h = 0) :
    ∫ a, max (a - h) 0 ∂ν ≤ 0 := by
  by_contra hU
  push Not at hU
  set U := ∫ a, max (a - h) 0 ∂ν with hUdef
  have hne : ¬ (capacitySet ν h).Nonempty := by
    intro hne
    obtain ⟨s, hs⟩ := hne
    have := Iface.le_capacity ν hν hs
    linarith [hs.1]
  -- r = mass above h
  set r := ν.real (Ioi h) with hr
  have hind : ∀ a, max (a - h) 0 = Set.indicator (Ioi h) (fun a => a - h) a := by
    intro a
    by_cases ha : h < a
    · rw [Set.indicator_of_mem (show a ∈ Ioi h from ha), max_eq_left (by linarith)]
    · rw [Set.indicator_of_notMem (show a ∉ Ioi h from ha), max_eq_right (by linarith [not_lt.1 ha])]
  have hr0 : 0 < r := by
    by_contra hr0
    have hr0' : r = 0 := le_antisymm (not_lt.1 hr0) measureReal_nonneg
    have : ν (Ioi h) = 0 := by
      have := (measureReal_eq_zero_iff (μ := ν) (s := Ioi h)).1 hr0'
      exact this
    have hae : ∀ᵐ a ∂ν, a ∉ Ioi h := by
      rw [← measure_eq_zero_iff_ae_notMem]; exact this
    have : U = 0 := by
      rw [hUdef]
      refine integral_eq_zero_of_ae ?_
      filter_upwards [hae] with a ha
      rw [hind a, Set.indicator_of_notMem ha]; rfl
    linarith
  have hr1 : r ≤ 1 := measureReal_le_one
  have hrs : r ∈ Ioc (0:ℝ) 1 := ⟨hr0, hr1⟩
  have hlt : poolMean ν r < h := by
    by_contra hge
    exact hne ⟨r, hr0, hr1, not_lt.1 hge⟩
  set w : ℝ → ℝ := Set.indicator (Ioi h) (fun _ => (1:ℝ)) with hw
  have hwm : Measurable w := measurable_const.indicator measurableSet_Ioi
  have hw01 : ∀ a, w a ∈ Icc (0:ℝ) 1 := by
    intro a
    by_cases ha : a ∈ Ioi h
    · rw [hw, Set.indicator_of_mem ha]; exact ⟨zero_le_one, le_rfl⟩
    · rw [hw, Set.indicator_of_notMem ha]; exact ⟨le_rfl, zero_le_one⟩
  have hmass : ∫ a, w a ∂ν = r := by
    rw [hw, integral_indicator measurableSet_Ioi]; simp [hr]
  have hb := Iface.selector_le_topSelector ν hν hwm hw01 hrs hmass (f := id) monotone_id hν
  rw [show (∫ z, topSelector ν r z * id z ∂ν) = r * poolMean ν r from
    CapExtra.integral_topSelector_mul ν hν hrs] at hb
  have hL : ∫ a, w a * id a ∂ν = U + h * r := by
    have : ∀ a, w a * id a = max (a - h) 0 + h * w a := by
      intro a
      by_cases ha : a ∈ Ioi h
      · rw [hw, Set.indicator_of_mem ha, max_eq_left (by simp at ha; linarith)]; simp
      · rw [hw, Set.indicator_of_notMem ha, max_eq_right (by simp at ha; linarith)]; simp
    simp_rw [this]
    rw [integral_add (integrable_pos_sub ν hν h) ((integrable_sel ν hwm hw01).const_mul h),
      integral_const_mul, hmass]
  rw [hL] at hb
  have := mul_lt_mul_of_pos_left hlt hr0
  linarith

/-- Balance on the top-`b` pool: `∫ w_b (h - a)^+ = ∫ (a - h)^+` when the pool mean is `h`. -/
theorem balance (hν : Integrable id ν) {b h : ℝ} (hb : b ∈ Ioc (0:ℝ) 1) (hm : poolMean ν b = h) :
    ∫ a, topSelector ν b a * max (h - a) 0 ∂ν = ∫ a, max (a - h) 0 ∂ν := by
  have hwm := measurable_topSelector ν b
  have hw01 := CapExtra.topSelector_mem_Icc ν hb
  have h1 : ∀ a, topSelector ν b a * max (a - h) 0 = max (a - h) 0 := by
    intro a
    by_cases ha : h < a
    · rw [Iface.topSelector_eq_one_of_gt ν hν hb (by rw [hm]; exact ha), one_mul]
    · rw [max_eq_right (by linarith [not_lt.1 ha])]; simp
  have h2 : ∀ a, topSelector ν b a * max (h - a) 0 =
      topSelector ν b a * max (a - h) 0 - topSelector ν b a * (a - h) := by
    intro a
    rcases le_total a h with h3 | h3
    · rw [max_eq_right (by linarith : a - h ≤ 0), max_eq_left (by linarith : (0:ℝ) ≤ h - a)]; ring
    · rw [max_eq_right (by linarith : h - a ≤ 0), max_eq_left (by linarith : (0:ℝ) ≤ a - h)]; ring
  have hint1 : Integrable (fun a => topSelector ν b a * max (a - h) 0) ν :=
    integrable_sel_mul ν hν hwm hw01 (integrable_pos_sub ν hν h)
  have hint2 : Integrable (fun a => topSelector ν b a * (a - h)) ν :=
    integrable_sel_mul ν hν hwm hw01 (hν.sub (integrable_const h))
  have h0 : ∫ a, topSelector ν b a * (a - h) ∂ν = 0 := by
    have : ∫ a, topSelector ν b a * (a - h) ∂ν =
        ∫ a, topSelector ν b a * a ∂ν - h * ∫ a, topSelector ν b a ∂ν := by
      rw [← integral_const_mul, ← integral_sub (integrable_sel_mul ν hν hwm hw01 (g := fun a => a) hν)
        ((integrable_sel ν hwm hw01).const_mul h)]
      congr 1; ext a; ring
    rw [this, CapExtra.integral_topSelector_mul ν hν hb, CapExtra.integral_topSelector ν hν hb, hm]
    ring
  simp_rw [h2]
  rw [integral_sub hint1 hint2, h0]
  simp_rw [h1]
  ring

/-- Step 2 for a single coordinate: compare the top-`b` pool with any weight `w'` of larger mass. -/
theorem tail_single (hν : Integrable id ν) (h b : ℝ) (hb : capacity ν h = b) (hb1 : b < 1)
    {w : ℝ → ℝ} (hwm : Measurable w) (hw01 : ∀ a, w a ∈ Icc (0:ℝ) 1) {M : ℝ}
    (hM : ∫ a, w a ∂ν = M) (hbM : b < M) {V : ℝ} (hV : ∫ a, w a * max (h - a) 0 ∂ν ≤ V) :
    ∫ a, max (a - h) 0 ∂ν ≤ b / M * V := by
  have hb0 : 0 ≤ b := hb ▸ (Iface.capacity_nonneg_le_one ν hν h).1
  rcases hb0.eq_or_lt with hz | hpos
  · rw [← hz] at hb ⊢
    simpa using U_zero_of_capacity_zero ν hν h hb
  have hne : (capacitySet ν h).Nonempty := by
    by_contra hne
    rw [Iface.capacity_eq_zero ν h hne] at hb
    linarith
  obtain ⟨hmem, hspec⟩ := Iface.capacity_spec ν hν h hne
  rw [hb] at hmem hspec
  have hbs : b ∈ Ioc (0:ℝ) 1 := ⟨hmem.1, hmem.2.1⟩
  have hpm : poolMean ν b = h := hspec hb1
  have hbal := balance ν hν hbs hpm
  have hMpos : 0 < M := by linarith
  set c := b / M with hc
  have hc0 : 0 ≤ c := by positivity
  have hc1 : c ≤ 1 := by rw [hc, div_le_one hMpos]; linarith
  have hw'm : Measurable (fun a => c * w a) := hwm.const_mul c
  have hw'01 : ∀ a, c * w a ∈ Icc (0:ℝ) 1 := fun a =>
    ⟨mul_nonneg hc0 (hw01 a).1, by nlinarith [(hw01 a).1, (hw01 a).2]⟩
  have hmass : ∫ a, c * w a ∂ν = b := by
    rw [integral_const_mul, hM, hc]; field_simp
  have hf : Monotone (fun a : ℝ => -max (h - a) 0) := by
    intro a a' haa
    simp only [neg_le_neg_iff]
    exact max_le_max (by linarith) le_rfl
  have hfi : Integrable (fun a : ℝ => -max (h - a) 0) ν := (integrable_neg_sub ν hν h).neg
  have hbath := Iface.selector_le_topSelector ν hν hw'm hw'01 hbs hmass hf hfi
  have e1 : ∫ a, c * w a * -max (h - a) 0 ∂ν = -(c * ∫ a, w a * max (h - a) 0 ∂ν) := by
    rw [← integral_const_mul, ← integral_neg]
    congr 1; ext a; ring
  have e2 : ∫ a, topSelector ν b a * -max (h - a) 0 ∂ν = -∫ a, max (a - h) 0 ∂ν := by
    rw [← hbal, ← integral_neg]
    congr 1; ext a; ring
  rw [e1, e2] at hbath
  have := mul_le_mul_of_nonneg_left hV hc0
  linarith

end PersuasionByParts.Known.Dev.CapTail1
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
noncomputable section

namespace PersuasionByParts.Known.Dev.Cap
open PersuasionByParts.Known

variable {n : ℕ} (P : Prior n)

theorem coords_iIndep : iIndepFun (fun (i : Fin n) (x : Fin n → ℝ) => x i) (priorLaw P) := by
  have := iIndepFun_pi (μ := P.marginal) (X := fun _ => (id : ℝ → ℝ)) (fun _ => aemeasurable_id)
  simpa [priorLaw] using this

theorem pair_law (i : Fin n) :
    (priorLaw P).map (fun x => (others i x, x i)) = (othersLaw P i).prod (P.marginal i) := by
  have hind : IndepFun (others i) (fun x => x i) (priorLaw P) := by
    have := (coords_iIndep P).indepFun_finsetSum_of_notMem (fun j => measurable_pi_apply j)
      (s := Finset.univ.erase i) (i := i) (Finset.notMem_erase i _)
    have e : others i = ∑ j ∈ Finset.univ.erase i, fun (x : Fin n → ℝ) => x j := by
      ext x; simp [others]
    rw [e]; exact this
  rw [indepFun_iff_map_prod_eq_prod_map_map (measurable_others i).aemeasurable
    (measurable_pi_apply i).aemeasurable] at hind
  rw [hind]
  unfold othersLaw
  congr 1
  rw [← (measurePreserving_eval P.marginal i).map_eq]
  rfl

/-- Fubini over the pair `(X_{-i}, X_i)`. -/
theorem integral_pair (i : Fin n) {G : ℝ × ℝ → ℝ} (hG : Measurable G)
    (hi : Integrable (fun x => G (others i x, x i)) (priorLaw P)) :
    ∫ x, G (others i x, x i) ∂priorLaw P = ∫ a, ∫ z, G (z, a) ∂(othersLaw P i) ∂(P.marginal i) := by
  have hm : Measurable (fun x : Fin n → ℝ => (others i x, x i)) :=
    (measurable_others i).prodMk (measurable_pi_apply i)
  have h1 : ∫ x, G (others i x, x i) ∂priorLaw P =
      ∫ p, G p ∂((priorLaw P).map (fun x => (others i x, x i))) := by
    rw [integral_map hm.aemeasurable hG.aestronglyMeasurable]
  rw [h1, pair_law]
  refine integral_prod_symm _ ?_
  rw [← pair_law]
  exact (integrable_map_measure hG.aestronglyMeasurable hm.aemeasurable).2 hi

end PersuasionByParts.Known.Dev.Cap
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
noncomputable section

namespace PersuasionByParts.Known.Dev.Cap
open PersuasionByParts.Known

variable {n : ℕ} (P : Prior n)

/-- the (unnormalised) joint weight `W(a + z) 1{z ≤ c}`. -/
def Kw (q c : ℝ) (a z : ℝ) : ℝ :=
  topSelector (sumLaw P) q (a + z) * Set.indicator (Iic c) (fun _ => (1:ℝ)) z

theorem measurable_Kw (q c : ℝ) : Measurable (fun p : ℝ × ℝ => Kw P q c p.1 p.2) := by
  unfold Kw
  exact (((measurable_topSelector _ _).comp (measurable_fst.add measurable_snd))).mul
    (measurable_const.indicator measurableSet_Iic |>.comp measurable_snd)

theorem Kw_mem (q c : ℝ) (hq : q ∈ Ioc 0 1) (a z : ℝ) : Kw P q c a z ∈ Icc (0:ℝ) 1 := by
  have h1 := CapExtra.topSelector_mem_Icc (sumLaw P) hq (a + z)
  unfold Kw
  by_cases hz : z ∈ Iic c
  · rw [Set.indicator_of_mem hz, mul_one]; exact h1
  · rw [Set.indicator_of_notMem hz, mul_zero]; exact ⟨le_rfl, zero_le_one⟩

/-- the weight `w'(a) = ∫ W(a + z) 1{z ≤ c} dρ(z)`. -/
def wprime (i : Fin n) (q c : ℝ) (a : ℝ) : ℝ := ∫ z, Kw P q c a z ∂(othersLaw P i)

theorem measurable_wprime (i : Fin n) (q c : ℝ) : Measurable (wprime P i q c) := by
  have h : Measurable (Function.uncurry (Kw P q c)) := measurable_Kw P q c
  exact (h.stronglyMeasurable.integral_prod_right').measurable

theorem wprime_mem (i : Fin n) (q c : ℝ) (hq : q ∈ Ioc 0 1) (a : ℝ) :
    wprime P i q c a ∈ Icc (0:ℝ) 1 := by
  unfold wprime
  refine ⟨integral_nonneg fun z => (Kw_mem P q c hq a z).1, ?_⟩
  calc ∫ z, Kw P q c a z ∂(othersLaw P i) ≤ ∫ z, (1:ℝ) ∂(othersLaw P i) :=
        integral_mono_of_nonneg (Eventually.of_forall fun z => (Kw_mem P q c hq a z).1)
          (integrable_const _) (Eventually.of_forall fun z => (Kw_mem P q c hq a z).2)
    _ = 1 := by simp

theorem Kw_pair (i : Fin n) (q c : ℝ) (x : Fin n → ℝ) :
    Kw P q c (x i) (others i x) =
      Wsel P q x * Set.indicator {x | others i x ≤ c} (fun _ => (1:ℝ)) x := by
  have : total x = x i + others i x := by
    unfold total others; rw [Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  unfold Kw Wsel
  rw [this]
  by_cases h : others i x ≤ c
  · rw [Set.indicator_of_mem (show others i x ∈ Iic c from h),
      Set.indicator_of_mem (show x ∈ {x | others i x ≤ c} from h)]
  · rw [Set.indicator_of_notMem (show others i x ∉ Iic c from h),
      Set.indicator_of_notMem (show x ∉ {x | others i x ≤ c} from h)]

/-- `∫ w'(a) g(a) dν = E[W 1{X_{-i} ≤ c} g(X_i)]`. -/
theorem integral_wprime_mul (i : Fin n) (q c : ℝ) (hq : q ∈ Ioc 0 1) {g : ℝ → ℝ}
    (hgm : Measurable g) (hg : Integrable g (P.marginal i)) :
    ∫ a, wprime P i q c a * g a ∂(P.marginal i) =
      ∫ x, Wsel P q x * Set.indicator {x | others i x ≤ c} (fun _ => (1:ℝ)) x * g (x i)
        ∂priorLaw P := by
  have hgP : Integrable (fun x : Fin n → ℝ => g (x i)) (priorLaw P) := by
    have h := hg
    rw [← (measurePreserving_eval P.marginal i).map_eq] at h
    have := (integrable_map_measure (μ := Measure.pi P.marginal) (f := Function.eval i)
      (g := g) hgm.aestronglyMeasurable (measurable_pi_apply i).aemeasurable).1 h
    exact this
  set G : ℝ × ℝ → ℝ := fun p => Kw P q c p.2 p.1 * g p.2 with hG
  have hGm : Measurable G := by
    have h1 : Measurable (fun p : ℝ × ℝ => Kw P q c p.2 p.1) :=
      (measurable_Kw P q c).comp measurable_swap
    exact h1.mul (hgm.comp measurable_snd)
  have hpt : ∀ x : Fin n → ℝ, G (others i x, x i) =
      Wsel P q x * Set.indicator {x | others i x ≤ c} (fun _ => (1:ℝ)) x * g (x i) := by
    intro x; simp only [hG]; rw [Kw_pair]
  have hint : Integrable (fun x => G (others i x, x i)) (priorLaw P) := by
    simp_rw [hpt]
    refine hgP.bdd_mul (c := 1) ?_ (Eventually.of_forall fun x => ?_)
    · exact ((measurable_Wsel P q).mul (measurable_const.indicator
        (measurableSet_le (measurable_others i) measurable_const))).aestronglyMeasurable
    · have := Kw_mem P q c hq (x i) (others i x)
      rw [Kw_pair] at this
      rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2
  have := integral_pair P i hGm hint
  simp_rw [hpt] at this
  rw [this]
  refine integral_congr_ae (Eventually.of_forall fun a => ?_)
  simp only [hG, wprime]
  rw [← integral_mul_const]

/-- Step 2: tail term, coordinatewise. -/
theorem tail_term (_hn : 0 < n) (q t : ℝ) (hq : q ∈ Ioc 0 1) (ht : t ≤ poolMean (sumLaw P) q)
    (hB : totalCapacity P q t < 2 * q / 3) (i : Fin n) :
    ∫ x, max (x - target P q t i) 0 ∂(P.marginal i) ≤
      coordinateCapacity P q t i * (3 * Uex P t / (2 * q)) := by
  set h := target P q t i with hh
  set c := t - h with hc
  have hν := P.finiteMean i
  have hq0 := hq.1
  have hq1 := hq.2
  have hb_le : coordinateCapacity P q t i ≤ totalCapacity P q t :=
    Finset.single_le_sum (f := fun j => coordinateCapacity P q t j)
      (fun j _ => coordinateCapacity_nonneg P q t j) (Finset.mem_univ i)
  have hb0 := coordinateCapacity_nonneg P q t i
  have hb1 : coordinateCapacity P q t i < 1 := by linarith
  have hind_meas : MeasurableSet {x : Fin n → ℝ | others i x ≤ c} :=
    measurableSet_le (measurable_others i) measurable_const
  have hWi := integrable_Wsel P q hq
  have hindi : Integrable (Set.indicator {x : Fin n → ℝ | others i x ≤ c} (fun _ => (1:ℝ)))
      (priorLaw P) := (integrable_const (1:ℝ)).indicator hind_meas
  have hWind : Integrable (fun x => Wsel P q x *
      Set.indicator {x : Fin n → ℝ | others i x ≤ c} (fun _ => (1:ℝ)) x) (priorLaw P) :=
    integrable_Wsel_mul P q hq hindi
  -- mass of w'
  have hM : 2 * q / 3 ≤ ∫ a, wprime P i q c a ∂(P.marginal i) := by
    have := integral_wprime_mul P i q c hq (g := fun _ => 1) measurable_const (integrable_const 1)
    simp only [mul_one] at this
    rw [this]
    have hc' : (priorLaw P).real {x | c < others i x} ≤ q / 3 := others_tail P q t hq i
    have hlow : ∫ x, (Wsel P q x - Set.indicator {x : Fin n → ℝ | c < others i x} (fun _ => (1:ℝ)) x)
        ∂priorLaw P ≤ ∫ x, Wsel P q x * Set.indicator {x : Fin n → ℝ | others i x ≤ c}
          (fun _ => (1:ℝ)) x ∂priorLaw P := by
      refine integral_mono (hWi.sub ((integrable_const (1:ℝ)).indicator
        (measurableSet_lt measurable_const (measurable_others i)))) hWind fun x => ?_
      have hw := Wsel_mem P q hq x
      by_cases hx : others i x ≤ c
      · rw [Set.indicator_of_mem (show x ∈ {x | others i x ≤ c} from hx),
          Set.indicator_of_notMem (show x ∉ {x | c < others i x} from not_lt.2 hx)]
        simp
      · rw [Set.indicator_of_notMem (show x ∉ {x | others i x ≤ c} from hx),
          Set.indicator_of_mem (show x ∈ {x | c < others i x} from not_le.1 hx)]
        simp only [mul_zero]; linarith [hw.2]
    have hsub : ∫ x, (Wsel P q x - Set.indicator {x : Fin n → ℝ | c < others i x}
        (fun _ => (1:ℝ)) x) ∂priorLaw P = q - (priorLaw P).real {x | c < others i x} := by
      rw [integral_sub hWi ((integrable_const (1:ℝ)).indicator
        (measurableSet_lt measurable_const (measurable_others i))), integral_Wsel P q hq,
        integral_indicator (measurableSet_lt measurable_const (measurable_others i))]
      simp
    linarith
  -- deficit bound
  have hdef : Integrable (fun x : Fin n → ℝ => max (h - x i) 0) (priorLaw P) :=
    ((integrable_const h).sub (integrable_coord P i)).pos_part
  have hWindm : ∀ x, Wsel P q x * Set.indicator {x : Fin n → ℝ | others i x ≤ c}
      (fun _ => (1:ℝ)) x ∈ Icc (0:ℝ) 1 := fun x => by
    have := Kw_mem P q c hq (x i) (others i x)
    rwa [Kw_pair] at this
  have hV : ∫ a, wprime P i q c a * max (h - a) 0 ∂(P.marginal i) ≤ Uex P t := by
    have hgm : Measurable (fun a : ℝ => max (h - a) 0) := by fun_prop
    rw [integral_wprime_mul P i q c hq hgm (CapTail1.integrable_neg_sub _ hν h)]
    refine le_trans (integral_mono ?_ ?_ (fun x => ?_)) (integral_Wsel_neg_le P q t hq ht)
    · exact hdef.bdd_mul (c := 1) (f := fun x => Wsel P q x * Set.indicator
        {x : Fin n → ℝ | others i x ≤ c} (fun _ => (1:ℝ)) x) hWind.aestronglyMeasurable
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (hWindm x).1]; exact (hWindm x).2)
    · exact integrable_Wsel_mul P q hq (((integrable_const t).sub (integrable_total P)).pos_part)
    · show Wsel P q x * Set.indicator {x : Fin n → ℝ | others i x ≤ c} (fun _ => (1:ℝ)) x *
          max (h - x i) 0 ≤ Wsel P q x * max (t - total x) 0
      have hw := Wsel_mem P q hq x
      by_cases hx : others i x ≤ c
      · rw [Set.indicator_of_mem (show x ∈ {x | others i x ≤ c} from hx), mul_one]
        refine mul_le_mul_of_nonneg_left (max_le_max ?_ le_rfl) hw.1
        have : total x = x i + others i x := by
          unfold total others; rw [Finset.add_sum_erase _ _ (Finset.mem_univ i)]
        rw [this, hc] at *
        linarith
      · rw [Set.indicator_of_notMem (show x ∉ {x | others i x ≤ c} from hx)]
        simp only [mul_zero, zero_mul]
        exact mul_nonneg hw.1 (le_max_right _ _)
  have hMpos : 0 < ∫ a, wprime P i q c a ∂(P.marginal i) := by linarith
  have hbM : coordinateCapacity P q t i < ∫ a, wprime P i q c a ∂(P.marginal i) := by linarith
  have key := CapTail1.tail_single (P.marginal i) hν h (coordinateCapacity P q t i) rfl hb1
    (measurable_wprime P i q c) (wprime_mem P i q c hq) rfl hbM hV
  refine le_trans key ?_
  have hU0 := Uex_nonneg P t
  have h1 : coordinateCapacity P q t i / (∫ a, wprime P i q c a ∂(P.marginal i)) ≤
      coordinateCapacity P q t i / (2 * q / 3) :=
    div_le_div_of_nonneg_left hb0 (by positivity) hM
  calc coordinateCapacity P q t i / (∫ a, wprime P i q c a ∂(P.marginal i)) * Uex P t
      ≤ coordinateCapacity P q t i / (2 * q / 3) * Uex P t := mul_le_mul_of_nonneg_right h1 hU0
    _ = coordinateCapacity P q t i * (3 * Uex P t / (2 * q)) := by field_simp

end PersuasionByParts.Known.Dev.Cap
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
noncomputable section

namespace PersuasionByParts.Known.Dev.Cap
open PersuasionByParts.Known

variable {n : ℕ} (P : Prior n)

/-- sum of the coordinates with index `< k`. -/
def Ssum (n k : ℕ) (x : Fin n → ℝ) : ℝ := ∑ j : Fin n, if j.val < k then x j else 0

/-- sum of the coordinates with index `≥ k`. -/
def Tsum (n k : ℕ) (x : Fin n → ℝ) : ℝ := ∑ j : Fin n, if k ≤ j.val then x j else 0

/-- the vector of the first `k` coordinates (others zeroed). -/
def Yk (n k : ℕ) (x : Fin n → ℝ) : Fin n → ℝ := fun j => if j.val < k then x j else 0

theorem Ssum_add_Tsum (k : ℕ) (x : Fin n → ℝ) : Ssum n k x + Tsum n k x = total x := by
  unfold Ssum Tsum total
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases h : j.val < k
  · simp [h, not_le.2 h]
  · simp [h, not_lt.1 h]

theorem measurable_Ssum (k : ℕ) : Measurable (Ssum n k) := by
  unfold Ssum
  refine Finset.measurable_sum _ fun j _ => ?_
  by_cases h : j.val < k
  · simp only [h, if_true]; exact measurable_pi_apply j
  · simp only [h, if_false]; exact measurable_const

theorem measurable_Tsum (k : ℕ) : Measurable (Tsum n k) := by
  unfold Tsum
  refine Finset.measurable_sum _ fun j _ => ?_
  by_cases h : k ≤ j.val
  · simp only [h, if_true]; exact measurable_pi_apply j
  · simp only [h, if_false]; exact measurable_const

theorem measurable_Yk (k : ℕ) : Measurable (Yk n k) := by
  refine measurable_pi_lambda _ fun j => ?_
  unfold Yk
  by_cases h : j.val < k
  · simp only [h, if_true]; exact measurable_pi_apply j
  · simp only [h, if_false]; exact measurable_const

theorem integrable_Ssum (k : ℕ) : Integrable (Ssum n k) (priorLaw P) := by
  unfold Ssum
  refine integrable_finsetSum _ fun j _ => ?_
  by_cases h : j.val < k
  · simp only [h, if_true]; exact integrable_coord P j
  · simp only [h, if_false]; exact integrable_const _

theorem integrable_Tsum (k : ℕ) : Integrable (Tsum n k) (priorLaw P) := by
  unfold Tsum
  refine integrable_finsetSum _ fun j _ => ?_
  by_cases h : k ≤ j.val
  · simp only [h, if_true]; exact integrable_coord P j
  · simp only [h, if_false]; exact integrable_const _

theorem indep_Yk_Tsum (k : ℕ) : IndepFun (Yk n k) (Tsum n k) (priorLaw P) := by
  classical
  set S : Finset (Fin n) := Finset.univ.filter (fun j => j.val < k) with hS
  set T : Finset (Fin n) := Finset.univ.filter (fun j => k ≤ j.val) with hT
  have hST : Disjoint S T := by
    rw [Finset.disjoint_filter]; intro j _ h1 h2; omega
  have h := (coords_iIndep P).indepFun_finset S T hST (fun j => measurable_pi_apply j)
  let φ1 : (S → ℝ) → (Fin n → ℝ) := fun y j => if hj : j ∈ S then y ⟨j, hj⟩ else 0
  let φ2 : (T → ℝ) → ℝ := fun y => ∑ j : T, y j
  have hφ1 : Measurable φ1 := by
    refine measurable_pi_lambda _ fun j => ?_
    by_cases hj : j ∈ S
    · simp only [φ1, hj, dite_true]; exact measurable_pi_apply _
    · simp only [φ1, hj, dite_false]; exact measurable_const
  have hφ2 : Measurable φ2 := Finset.measurable_sum _ fun j _ => measurable_pi_apply j
  have := h.comp hφ1 hφ2
  convert this using 1
  · ext x j
    simp only [Yk, Function.comp, φ1, hS, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases hj : j.val < k <;> simp [hj]
  · ext x
    simp only [Tsum, Function.comp, φ2]
    rw [Finset.sum_coe_sort T (fun j => x j), hT, Finset.sum_filter]

theorem decouple (k : ℕ) {H : (Fin n → ℝ) → ℝ → ℝ}
    (hH : Measurable (fun p : (Fin n → ℝ) × ℝ => H p.1 p.2))
    (hdet : ∀ x x' : Fin n → ℝ, (∀ j : Fin n, j.val < k → x j = x' j) → ∀ r, H x r = H x' r)
    (hint : Integrable (fun x => H x (Tsum n k x)) (priorLaw P)) :
    ∫ x, H x (Tsum n k x) ∂priorLaw P =
      ∫ x, ∫ y, H x (Tsum n k y) ∂priorLaw P ∂priorLaw P := by
  have hY : ∀ x, H x = H (Yk n k x) := fun x => funext fun r =>
    hdet x (Yk n k x) (fun j hj => by simp [Yk, hj]) r
  have hind := indep_Yk_Tsum P k
  rw [indepFun_iff_map_prod_eq_prod_map_map (measurable_Yk k).aemeasurable
    (measurable_Tsum k).aemeasurable] at hind
  have hm : Measurable (fun x : Fin n → ℝ => (Yk n k x, Tsum n k x)) :=
    (measurable_Yk k).prodMk (measurable_Tsum k)
  set F : (Fin n → ℝ) × ℝ → ℝ := fun p => H p.1 p.2 with hF
  have e1 : ∫ x, H x (Tsum n k x) ∂priorLaw P = ∫ x, F (Yk n k x, Tsum n k x) ∂priorLaw P := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hF]; rw [← hY x]
  have hint' : Integrable (fun x => F (Yk n k x, Tsum n k x)) (priorLaw P) := by
    refine hint.congr (Eventually.of_forall fun x => ?_)
    simp only [hF]; rw [← hY x]
  have e2 : ∫ x, F (Yk n k x, Tsum n k x) ∂priorLaw P =
      ∫ p, F p ∂((priorLaw P).map (fun x => (Yk n k x, Tsum n k x))) := by
    rw [integral_map hm.aemeasurable hH.aestronglyMeasurable]
  have hintm : Integrable F (((priorLaw P).map (Yk n k)).prod ((priorLaw P).map (Tsum n k))) := by
    rw [← hind]
    exact (integrable_map_measure hH.aestronglyMeasurable hm.aemeasurable).2 hint'
  rw [e1, e2, hind, integral_prod _ hintm]
  have hg : Measurable (fun y : Fin n → ℝ => ∫ r, F (y, r) ∂((priorLaw P).map (Tsum n k))) :=
    (hH.stronglyMeasurable.integral_prod_right' (ν := (priorLaw P).map (Tsum n k))).measurable
  rw [integral_map (measurable_Yk k).aemeasurable hg.aestronglyMeasurable]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  have hFx : Measurable (fun r : ℝ => F (Yk n k x, r)) :=
    hH.comp (measurable_const.prodMk measurable_id)
  rw [integral_map (φ := Tsum n k) (f := fun r : ℝ => F (Yk n k x, r)) (measurable_Tsum k).aemeasurable
    hFx.aestronglyMeasurable]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [hF]; rw [← hY x]

end PersuasionByParts.Known.Dev.Cap
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
noncomputable section

namespace PersuasionByParts.Known.Dev.Cap
open PersuasionByParts.Known

variable {n : ℕ} (P : Prior n)

/-- `G_k(z) = P(z + X_{≥k} ≥ t)`. -/
def Gf (t : ℝ) (k : ℕ) (z : ℝ) : ℝ := (priorLaw P).real {x | t ≤ z + Tsum n k x}

/-- `φ_k(z) = E[(z + X_{≥k} - t)^+]`. -/
def phi (t : ℝ) (k : ℕ) (z : ℝ) : ℝ := ∫ x, max (z + Tsum n k x - t) 0 ∂priorLaw P

theorem integrable_phi_aux (t : ℝ) (k : ℕ) (z : ℝ) :
    Integrable (fun x => max (z + Tsum n k x - t) 0) (priorLaw P) :=
  (((integrable_const z).add (integrable_Tsum P k)).sub (integrable_const t)).pos_part

theorem phi_nonneg (t : ℝ) (k : ℕ) (z : ℝ) : 0 ≤ phi P t k z :=
  integral_nonneg fun _ => le_max_right _ _

theorem phi_le (t : ℝ) (k : ℕ) (a b : ℝ) : phi P t k a ≤ phi P t k b + max (a - b) 0 := by
  unfold phi
  have h1 := integrable_phi_aux P t k a
  have h2 := integrable_phi_aux P t k b
  calc ∫ x, max (a + Tsum n k x - t) 0 ∂priorLaw P
      ≤ ∫ x, (max (b + Tsum n k x - t) 0 + max (a - b) 0) ∂priorLaw P := by
        refine integral_mono h1 (h2.add (integrable_const _)) fun x => ?_
        show max (a + Tsum n k x - t) 0 ≤ max (b + Tsum n k x - t) 0 + max (a - b) 0
        rcases le_total (a + Tsum n k x - t) 0 with h | h
        · rw [max_eq_right h]
          exact add_nonneg (le_max_right _ _) (le_max_right _ _)
        · rw [max_eq_left h]
          have := le_max_left (b + Tsum n k x - t) 0
          have := le_max_left (a - b) 0
          have := le_max_right (b + Tsum n k x - t) 0
          have := le_max_right (a - b) 0
          rcases le_total (a - b) 0 with h3 | h3
          · rw [max_eq_right h3]; linarith [le_max_left (b + Tsum n k x - t) 0]
          · rw [max_eq_left h3]; linarith [le_max_left (b + Tsum n k x - t) 0]
    _ = _ := by rw [integral_add h2 (integrable_const _)]; simp

theorem measurable_phi (t : ℝ) (k : ℕ) : Measurable (phi P t k) := by
  have : Measurable (fun p : ℝ × (Fin n → ℝ) => max (p.1 + Tsum n k p.2 - t) 0) := by
    have := measurable_Tsum (n := n) k
    fun_prop
  exact (this.stronglyMeasurable.integral_prod_right' (ν := priorLaw P)).measurable

theorem integrable_phi_Ssum (t : ℝ) (k m : ℕ) :
    Integrable (fun x => phi P t k (Ssum n m x)) (priorLaw P) := by
  refine ((integrable_const (phi P t k 0)).add (integrable_Ssum P m).norm).mono'
    ((measurable_phi P t k).comp (measurable_Ssum m)).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (phi_nonneg P t k _)]
  have := phi_le P t k (Ssum n m x) 0
  have h2 : max (Ssum n m x - 0) 0 ≤ ‖Ssum n m x‖ := by
    rw [Real.norm_eq_abs, sub_zero]; exact max_le (le_abs_self _) (abs_nonneg _)
  simp only [Pi.add_apply]; linarith

theorem integral_phi_Ssum (t : ℝ) (k : ℕ) :
    ∫ x, phi P t k (Ssum n k x) ∂priorLaw P = Uex P t := by
  have hH : Measurable (fun p : (Fin n → ℝ) × ℝ => max (Ssum n k p.1 + p.2 - t) 0) := by
    have := measurable_Ssum (n := n) k
    fun_prop
  have := decouple P k (H := fun x r => max (Ssum n k x + r - t) 0) hH
    (fun x x' hxx r => by
      have : Ssum n k x = Ssum n k x' := by
        unfold Ssum
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : j.val < k
        · simp [hj, hxx j hj]
        · simp [hj]
      simp only [this])
    (by
      refine (integrable_pos P t).congr (Eventually.of_forall fun x => ?_)
      simp only [Ssum_add_Tsum])
  unfold Uex
  have e : ∫ x, max (total x - t) 0 ∂priorLaw P =
      ∫ x, max (Ssum n k x + Tsum n k x - t) 0 ∂priorLaw P := by
    simp only [Ssum_add_Tsum]
  rw [e, this]
  rfl

theorem Ssum_succ (i : Fin n) (x : Fin n → ℝ) : Ssum n (i.val + 1) x = Ssum n i.val x + x i := by
  unfold Ssum
  have : ∀ j : Fin n, (if j.val < i.val + 1 then x j else 0) =
      (if j.val < i.val then x j else 0) + (if j = i then x j else 0) := by
    intro j
    by_cases h1 : j = i
    · subst h1; simp
    · have : j.val ≠ i.val := fun h => h1 (Fin.ext h)
      by_cases h2 : j.val < i.val
      · simp [h2, h1, show j.val < i.val + 1 by omega]
      · simp [h2, h1, show ¬ j.val < i.val + 1 by omega]
  simp_rw [this]
  rw [Finset.sum_add_distrib]
  simp

theorem Tsum_eq (i : Fin n) (x : Fin n → ℝ) : Tsum n i.val x = x i + Tsum n (i.val + 1) x := by
  have h := Ssum_add_Tsum (n := n) i.val x
  have h2 := Ssum_add_Tsum (n := n) (i.val + 1) x
  rw [Ssum_succ] at h2
  linarith

theorem others_eq (i : Fin n) (x : Fin n → ℝ) :
    others i x = Ssum n i.val x + Tsum n (i.val + 1) x := by
  have h := Ssum_add_Tsum (n := n) i.val x
  have h2 := Tsum_eq i x
  have : total x = x i + others i x := by
    unfold total others; rw [Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  linarith

end PersuasionByParts.Known.Dev.Cap
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
noncomputable section

namespace PersuasionByParts.Known.Dev.Cap
open PersuasionByParts.Known

variable {n : ℕ} (P : Prior n)

theorem measureReal_ind (s : Set (Fin n → ℝ)) (hs : MeasurableSet s) :
    ∫ x, Set.indicator s (fun _ => (1:ℝ)) x ∂priorLaw P = (priorLaw P).real s := by
  rw [integral_indicator hs]; simp

/-- (F3): if `G_i(z) < q/3` then `φ_{i+1}(z + h_i) ≤ 9U/q`. -/
theorem phi_bound (q t : ℝ) (hq : q ∈ Ioc 0 1) (ht : t ≤ poolMean (sumLaw P) q)
    (h : Fin n → ℝ) (hH1 : ∀ i, (priorLaw P).real {x | t - h i < others i x} ≤ q / 3)
    (i : Fin n) (z : ℝ) (hz : Gf P t i.val z < q / 3) :
    phi P t (i.val + 1) (z + h i) ≤ 9 * Uex P t / q := by
  have hq0 := hq.1
  set c := t - h i with hc
  set A : Set (Fin n → ℝ) := {x | others i x ≤ c ∧ z + Tsum n i.val x < t} with hA
  have hB1m : MeasurableSet {x : Fin n → ℝ | c < others i x} :=
    measurableSet_lt measurable_const (measurable_others i)
  have hB2m : MeasurableSet {x : Fin n → ℝ | t ≤ z + Tsum n i.val x} :=
    measurableSet_le measurable_const (measurable_const.add (measurable_Tsum _))
  have hAm : MeasurableSet A := by
    have : A = {x : Fin n → ℝ | c < others i x}ᶜ ∩ {x : Fin n → ℝ | t ≤ z + Tsum n i.val x}ᶜ := by
      ext x; simp [hA, not_lt, not_le]
    rw [this]; exact hB1m.compl.inter hB2m.compl
  set Az : (Fin n → ℝ) → ℝ := A.indicator (Wsel P q) with hAz
  have hW := Wsel_mem P q hq
  have hAz01 : ∀ x, Az x ∈ Icc (0:ℝ) 1 := fun x => by
    by_cases hx : x ∈ A
    · rw [hAz, Set.indicator_of_mem hx]; exact hW x
    · rw [hAz, Set.indicator_of_notMem hx]; exact ⟨le_rfl, zero_le_one⟩
  have hAzW : ∀ x, Az x ≤ Wsel P q x := fun x => by
    by_cases hx : x ∈ A
    · rw [hAz, Set.indicator_of_mem hx]
    · rw [hAz, Set.indicator_of_notMem hx]; exact (hW x).1
  have hAzm : Measurable Az := (measurable_Wsel P q).indicator hAm
  have hAzi : Integrable Az (priorLaw P) := (integrable_Wsel P q hq).indicator hAm
  have hAzmul : ∀ {g : (Fin n → ℝ) → ℝ}, Integrable g (priorLaw P) →
      Integrable (fun x => Az x * g x) (priorLaw P) := fun {g} hg =>
    hg.bdd_mul (c := 1) hAzm.aestronglyMeasurable (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hAz01 x).1]; exact (hAz01 x).2)
  -- mass
  have hmass : q / 3 < ∫ x, Az x ∂priorLaw P := by
    have hB1 := hH1 i
    have h1 : ∫ x, (Wsel P q x - Set.indicator {x : Fin n → ℝ | c < others i x} (fun _ => (1:ℝ)) x
        - Set.indicator {x : Fin n → ℝ | t ≤ z + Tsum n i.val x} (fun _ => (1:ℝ)) x) ∂priorLaw P ≤
        ∫ x, Az x ∂priorLaw P := by
      refine integral_mono ((integrable_Wsel P q hq).sub ((integrable_const (1:ℝ)).indicator hB1m)
        |>.sub ((integrable_const (1:ℝ)).indicator hB2m)) hAzi fun x => ?_
      show Wsel P q x - _ - _ ≤ Az x
      have hw := hW x
      by_cases hx : x ∈ A
      · have h1 : x ∉ {x : Fin n → ℝ | c < others i x} := fun h' => by
          have := hx.1; simp only [Set.mem_setOf_eq] at h'; linarith
        have h2 : x ∉ {x : Fin n → ℝ | t ≤ z + Tsum n i.val x} := fun h' => by
          have := hx.2; simp only [Set.mem_setOf_eq] at h'; linarith
        rw [hAz, Set.indicator_of_mem hx, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
        simp
      · have : x ∈ {x : Fin n → ℝ | c < others i x} ∨ x ∈ {x : Fin n → ℝ | t ≤ z + Tsum n i.val x} := by
          by_contra hcon
          push Not at hcon
          apply hx
          refine ⟨?_, ?_⟩
          · have := hcon.1; simp only [mem_setOf_eq, not_lt] at this; exact this
          · have := hcon.2; simp only [mem_setOf_eq, not_le] at this; exact this
        rw [hAz, Set.indicator_of_notMem hx]
        rcases this with h' | h'
        · rw [Set.indicator_of_mem h']
          have : 0 ≤ Set.indicator {x : Fin n → ℝ | t ≤ z + Tsum n i.val x} (fun _ => (1:ℝ)) x :=
            Set.indicator_nonneg (fun _ _ => zero_le_one) x
          linarith [hw.2]
        · rw [Set.indicator_of_mem h']
          have : 0 ≤ Set.indicator {x : Fin n → ℝ | c < others i x} (fun _ => (1:ℝ)) x :=
            Set.indicator_nonneg (fun _ _ => zero_le_one) x
          linarith [hw.2]
    have h2 : ∫ x, (Wsel P q x - Set.indicator {x : Fin n → ℝ | c < others i x} (fun _ => (1:ℝ)) x
        - Set.indicator {x : Fin n → ℝ | t ≤ z + Tsum n i.val x} (fun _ => (1:ℝ)) x) ∂priorLaw P =
        q - (priorLaw P).real {x | c < others i x} - (priorLaw P).real {x | t ≤ z + Tsum n i.val x} := by
      have hI1 : Integrable (Set.indicator {x : Fin n → ℝ | c < others i x} (fun _ => (1:ℝ)))
          (priorLaw P) := (integrable_const (1:ℝ)).indicator hB1m
      have hI2 : Integrable (Set.indicator {x : Fin n → ℝ | t ≤ z + Tsum n i.val x} (fun _ => (1:ℝ)))
          (priorLaw P) := (integrable_const (1:ℝ)).indicator hB2m
      have i1 : ∫ x, (Wsel P q x - Set.indicator {x : Fin n → ℝ | c < others i x} (fun _ => (1:ℝ)) x
          - Set.indicator {x : Fin n → ℝ | t ≤ z + Tsum n i.val x} (fun _ => (1:ℝ)) x) ∂priorLaw P =
          ∫ x, (Wsel P q x - Set.indicator {x : Fin n → ℝ | c < others i x} (fun _ => (1:ℝ)) x)
            ∂priorLaw P - ∫ x, Set.indicator {x : Fin n → ℝ | t ≤ z + Tsum n i.val x}
              (fun _ => (1:ℝ)) x ∂priorLaw P :=
        integral_sub ((integrable_Wsel P q hq).sub hI1) hI2
      have i2 : ∫ x, (Wsel P q x - Set.indicator {x : Fin n → ℝ | c < others i x} (fun _ => (1:ℝ)) x)
            ∂priorLaw P = ∫ x, Wsel P q x ∂priorLaw P - ∫ x, Set.indicator
              {x : Fin n → ℝ | c < others i x} (fun _ => (1:ℝ)) x ∂priorLaw P :=
        integral_sub (integrable_Wsel P q hq) hI1
      rw [i1, i2, integral_Wsel P q hq, measureReal_ind P _ hB1m, measureReal_ind P _ hB2m]
    have hGz : (priorLaw P).real {x | t ≤ z + Tsum n i.val x} < q / 3 := hz
    linarith
  -- pointwise inequality
  have hpt : ∀ x, Az x * phi P t (i.val + 1) (z + h i) ≤
      Az x * (phi P t (i.val + 1) (Ssum n (i.val + 1) x) + 2 * max (t - total x) 0) := by
    intro x
    by_cases hx : x ∈ A
    · apply mul_le_mul_of_nonneg_left _ (hAz01 x).1
      have h1 := phi_le P t (i.val + 1) (z + h i) (Ssum n (i.val + 1) x)
      have e1 := Ssum_succ i x
      have e2 := Tsum_eq i x
      have e3 := others_eq i x
      have e4 := Ssum_add_Tsum (n := n) i.val x
      have hx1 := hx.1
      have hx2 := hx.2
      have hd : z + h i - Ssum n (i.val + 1) x ≤ 2 * (t - total x) := by
        rw [hc] at hx1
        linarith
      have : max (z + h i - Ssum n (i.val + 1) x) 0 ≤ 2 * max (t - total x) 0 := by
        refine max_le (le_trans hd ?_) (by positivity)
        linarith [le_max_left (t - total x) 0]
      linarith
    · rw [hAz, Set.indicator_of_notMem hx]; simp
  have hint1 : Integrable (fun x => Az x * phi P t (i.val + 1) (Ssum n (i.val + 1) x)) (priorLaw P) :=
    hAzmul (integrable_phi_Ssum P t (i.val + 1) (i.val + 1))
  have hint2 : Integrable (fun x => Az x * max (t - total x) 0) (priorLaw P) :=
    hAzmul (((integrable_const t).sub (integrable_total P)).pos_part)
  have I1 : ∫ x, Az x * phi P t (i.val + 1) (Ssum n (i.val + 1) x) ∂priorLaw P ≤ Uex P t := by
    rw [← integral_phi_Ssum P t (i.val + 1)]
    refine integral_mono hint1 (integrable_phi_Ssum P t (i.val + 1) (i.val + 1)) fun x => ?_
    have := phi_nonneg P t (i.val + 1) (Ssum n (i.val + 1) x)
    show Az x * _ ≤ _
    nlinarith [(hAz01 x).1, (hAz01 x).2]
  have I2 : ∫ x, Az x * max (t - total x) 0 ∂priorLaw P ≤ Uex P t := by
    refine le_trans (integral_mono hint2
      (integrable_Wsel_mul P q hq (((integrable_const t).sub (integrable_total P)).pos_part))
      fun x => ?_) (integral_Wsel_neg_le P q t hq ht)
    show Az x * _ ≤ Wsel P q x * _
    exact mul_le_mul_of_nonneg_right (hAzW x) (le_max_right _ _)
  have hmain : phi P t (i.val + 1) (z + h i) * ∫ x, Az x ∂priorLaw P ≤ 3 * Uex P t := by
    have : ∫ x, Az x * phi P t (i.val + 1) (z + h i) ∂priorLaw P ≤
        ∫ x, Az x * (phi P t (i.val + 1) (Ssum n (i.val + 1) x) + 2 * max (t - total x) 0) ∂priorLaw P :=
      integral_mono (hAzi.mul_const _) (by
        simp_rw [mul_add]
        exact hint1.add ((hint2.const_mul 2).congr (Eventually.of_forall fun x => by ring))) hpt
    have e1 : ∫ x, Az x * phi P t (i.val + 1) (z + h i) ∂priorLaw P =
        (∫ x, Az x ∂priorLaw P) * phi P t (i.val + 1) (z + h i) := integral_mul_const _ _
    have e2 : ∫ x, Az x * (phi P t (i.val + 1) (Ssum n (i.val + 1) x) + 2 * max (t - total x) 0)
        ∂priorLaw P = ∫ x, Az x * phi P t (i.val + 1) (Ssum n (i.val + 1) x) ∂priorLaw P +
          2 * ∫ x, Az x * max (t - total x) 0 ∂priorLaw P := by
      rw [← integral_const_mul, ← integral_add hint1 (hint2.const_mul 2)]
      congr 1; ext x; ring
    linarith
  have hphi0 := phi_nonneg P t (i.val + 1) (z + h i)
  have : phi P t (i.val + 1) (z + h i) * (q / 3) ≤ 3 * Uex P t :=
    le_trans (mul_le_mul_of_nonneg_left hmass.le hphi0) hmain
  rw [le_div_iff₀ hq0]
  linarith

end PersuasionByParts.Known.Dev.Cap
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
noncomputable section

namespace PersuasionByParts.Known.Dev.Cap
open PersuasionByParts.Known

variable {n : ℕ} (P : Prior n)

theorem Ssum_congr (k : ℕ) {x x' : Fin n → ℝ} (h : ∀ j : Fin n, j.val < k → x j = x' j) :
    Ssum n k x = Ssum n k x' := by
  unfold Ssum
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j.val < k
  · simp [hj, h j hj]
  · simp [hj]

theorem Gf_mono (t : ℝ) (k : ℕ) : Monotone (Gf P t k) := by
  intro z z' hzz
  unfold Gf
  refine measureReal_mono (fun x hx => ?_)
  simp only [Set.mem_setOf_eq] at hx ⊢
  linarith

theorem measurable_Gf (t : ℝ) (k : ℕ) : Measurable (Gf P t k) := (Gf_mono P t k).measurable

variable (q t : ℝ)

/-- the stopping condition at level `k`. -/
def epsSet (k : ℕ) : Set (Fin n → ℝ) := {x | q / 3 ≤ Gf P t k (Ssum n k x)}

theorem measurableSet_epsSet (k : ℕ) : MeasurableSet (epsSet P q t k) :=
  measurableSet_le measurable_const ((measurable_Gf P t k).comp (measurable_Ssum k))

/-- the first-stop event `E_i`. -/
def Ev (i : ℕ) : Set (Fin n → ℝ) :=
  (⋂ k ∈ Finset.range (i + 1), (epsSet P q t k)ᶜ) ∩ epsSet P q t (i + 1)

theorem mem_Ev {i : ℕ} {x : Fin n → ℝ} :
    x ∈ Ev P q t i ↔ (∀ k, k ≤ i → x ∉ epsSet P q t k) ∧ x ∈ epsSet P q t (i + 1) := by
  unfold Ev
  simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff, Finset.mem_range]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨fun k hk => h1 k (by omega), h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨fun k hk => h1 k (by omega), h2⟩

theorem measurableSet_Ev (i : ℕ) : MeasurableSet (Ev P q t i) := by
  unfold Ev
  exact (Finset.measurableSet_biInter _ fun k _ => (measurableSet_epsSet P q t k).compl).inter
    (measurableSet_epsSet P q t (i + 1))

theorem Ev_congr {i : ℕ} {x x' : Fin n → ℝ} (h : ∀ j : Fin n, j.val < i + 1 → x j = x' j) :
    x ∈ Ev P q t i ↔ x' ∈ Ev P q t i := by
  have hk : ∀ k, k ≤ i + 1 → (x ∈ epsSet P q t k ↔ x' ∈ epsSet P q t k) := by
    intro k hk
    have : Ssum n k x = Ssum n k x' := Ssum_congr k (fun j hj => h j (by omega))
    simp only [epsSet, Set.mem_setOf_eq, this]
  rw [mem_Ev, mem_Ev]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun k hki hx => h1 k hki ((hk k (by omega)).2 hx), (hk _ le_rfl).1 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun k hki hx => h1 k hki ((hk k (by omega)).1 hx), (hk _ le_rfl).2 h2⟩

theorem Ev_disj {i j : ℕ} {x : Fin n → ℝ} (hi : x ∈ Ev P q t i) (hj : x ∈ Ev P q t j) : i = j := by
  rw [mem_Ev] at hi hj
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · exact hj.1 (i + 1) (by omega) hi.2
  · exact hi.1 (j + 1) (by omega) hj.2

theorem Ev_lt {i : ℕ} {x : Fin n → ℝ} (hx : x ∈ Ev P q t i) : Gf P t i (Ssum n i x) < q / 3 := by
  rw [mem_Ev] at hx
  have := hx.1 i le_rfl
  simpa [epsSet] using this

theorem Ev_ge {i : ℕ} {x : Fin n → ℝ} (hx : x ∈ Ev P q t i) :
    q / 3 ≤ Gf P t (i + 1) (Ssum n (i + 1) x) := by
  rw [mem_Ev] at hx
  exact hx.2

theorem Tsum_zero (x : Fin n → ℝ) : Tsum n 0 x = total x := by
  unfold Tsum total; simp

theorem Tsum_self (x : Fin n → ℝ) : Tsum n n x = 0 := by
  unfold Tsum
  refine Finset.sum_eq_zero fun j _ => ?_
  have := j.isLt
  simp [not_le.2 this]

theorem Ssum_zero (x : Fin n → ℝ) : Ssum n 0 x = 0 := by
  unfold Ssum; simp

theorem Ssum_self (x : Fin n → ℝ) : Ssum n n x = total x := by
  unfold Ssum total
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [j.isLt]

theorem Ev_cover (hq : q ∈ Ioc 0 1) (hp : revelationProbability P t < q / 3) {x : Fin n → ℝ}
    (hx : t ≤ total x) : ∃ i : Fin n, x ∈ Ev P q t i.val := by
  classical
  have hex : ∃ k, x ∈ epsSet P q t k := by
    refine ⟨n, ?_⟩
    simp only [epsSet, Set.mem_setOf_eq, Gf, Tsum_self, Ssum_self]
    have : {y : Fin n → ℝ | t ≤ total x + 0} = univ := by
      ext y; simp [hx]
    rw [this]; simp; linarith [hq.2]
  set k0 := Nat.find hex with hk0
  have hk0mem : x ∈ epsSet P q t k0 := Nat.find_spec hex
  have hk0pos : 0 < k0 := by
    by_contra h0
    have : k0 = 0 := by omega
    rw [this] at hk0mem
    simp only [epsSet, Set.mem_setOf_eq, Gf, Tsum_zero, Ssum_zero, zero_add] at hk0mem
    have : revelationProbability P t = (priorLaw P).real {y | t ≤ total y} := rfl
    linarith
  have hk0le : k0 ≤ n := Nat.find_min' hex (by
    simp only [epsSet, Set.mem_setOf_eq, Gf, Tsum_self, Ssum_self]
    have : {y : Fin n → ℝ | t ≤ total x + 0} = univ := by
      ext y; simp [hx]
    rw [this]; simp; linarith [hq.2])
  refine ⟨⟨k0 - 1, by omega⟩, ?_⟩
  rw [mem_Ev]
  refine ⟨fun k hk hmem => ?_, by simpa [Nat.sub_add_cancel hk0pos] using hk0mem⟩
  have : k0 ≤ k := Nat.find_min' hex hmem
  simp only at hk
  omega

end PersuasionByParts.Known.Dev.Cap
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
noncomputable section

namespace PersuasionByParts.Known.Dev.Cap
open PersuasionByParts.Known

variable {n : ℕ} (P : Prior n)

theorem integrable_of_bdd {f : (Fin n → ℝ) → ℝ} (hm : Measurable f) {B : ℝ}
    (hb : ∀ x, ‖f x‖ ≤ B) : Integrable f (priorLaw P) :=
  (integrable_const B).mono' hm.aestronglyMeasurable (Eventually.of_forall hb)

variable (q t : ℝ)

/-- (F1) for one `i`: `(q/3) P(E_i) ≤ P(E_i ∩ {X ≥ t})`. -/
theorem F1_one (i : ℕ) :
    q / 3 * (priorLaw P).real (Ev P q t i) ≤
      (priorLaw P).real (Ev P q t i ∩ {x | t ≤ total x}) := by
  set S : Set ((Fin n → ℝ) × ℝ) :=
    {p | p.1 ∈ Ev P q t i ∧ t ≤ Ssum n (i + 1) p.1 + p.2} with hS
  have hSm : MeasurableSet S :=
    ((measurableSet_Ev P q t i).preimage measurable_fst).inter
      (measurableSet_le measurable_const (((measurable_Ssum (i + 1)).comp measurable_fst).add measurable_snd))
  have hH : Measurable (fun p : (Fin n → ℝ) × ℝ =>
      Set.indicator S (fun _ => (1:ℝ)) (p.1, p.2)) := measurable_const.indicator hSm
  have hdet : ∀ x x' : Fin n → ℝ, (∀ j : Fin n, j.val < i + 1 → x j = x' j) → ∀ r,
      Set.indicator S (fun _ => (1:ℝ)) (x, r) = Set.indicator S (fun _ => (1:ℝ)) (x', r) := by
    intro x x' hxx r
    have h1 := Ev_congr P q t hxx
    have h2 : Ssum n (i + 1) x = Ssum n (i + 1) x' := Ssum_congr _ hxx
    have : (x, r) ∈ S ↔ (x', r) ∈ S := by simp only [hS, Set.mem_setOf_eq, h1, h2]
    by_cases hx : (x, r) ∈ S
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (this.1 hx)]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (this.2 h))]
  have hint : Integrable (fun x => Set.indicator S (fun _ => (1:ℝ)) (x, Tsum n (i + 1) x))
      (priorLaw P) := by
    refine integrable_of_bdd P (hH.comp (measurable_id.prodMk (measurable_Tsum (i + 1)))) (B := 1)
      fun x => ?_
    show ‖Set.indicator S (fun _ => (1:ℝ)) (x, Tsum n (i + 1) x)‖ ≤ 1
    by_cases hx : (x, Tsum n (i + 1) x) ∈ S
    · rw [Set.indicator_of_mem hx]; simp
    · rw [Set.indicator_of_notMem hx]; simp
  have hdec := decouple P (i + 1) (H := fun x r => Set.indicator S (fun _ => (1:ℝ)) (x, r)) hH hdet hint
  have eL : ∫ x, Set.indicator S (fun _ => (1:ℝ)) (x, Tsum n (i + 1) x) ∂priorLaw P =
      (priorLaw P).real (Ev P q t i ∩ {x | t ≤ total x}) := by
    rw [← measureReal_ind P _ ((measurableSet_Ev P q t i).inter
      (measurableSet_le measurable_const measurable_total))]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have : (x, Tsum n (i + 1) x) ∈ S ↔ x ∈ Ev P q t i ∩ {x | t ≤ total x} := by
      simp only [hS, Set.mem_setOf_eq, Set.mem_inter_iff, Ssum_add_Tsum]
    show Set.indicator S (fun _ => (1:ℝ)) (x, Tsum n (i + 1) x) = _
    by_cases hx : x ∈ Ev P q t i ∩ {x | t ≤ total x}
    · rw [Set.indicator_of_mem (this.2 hx), Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem (fun h => hx (this.1 h)), Set.indicator_of_notMem hx]
  have eR : ∀ x, ∫ y, Set.indicator S (fun _ => (1:ℝ)) (x, Tsum n (i + 1) y) ∂priorLaw P =
      Set.indicator (Ev P q t i) (fun x => Gf P t (i + 1) (Ssum n (i + 1) x)) x := by
    intro x
    by_cases hx : x ∈ Ev P q t i
    · rw [Set.indicator_of_mem hx]
      have : ∀ y, Set.indicator S (fun _ => (1:ℝ)) (x, Tsum n (i + 1) y) =
          Set.indicator {y | t ≤ Ssum n (i + 1) x + Tsum n (i + 1) y} (fun _ => (1:ℝ)) y := by
        intro y
        by_cases hy : t ≤ Ssum n (i + 1) x + Tsum n (i + 1) y
        · rw [Set.indicator_of_mem (show (x, Tsum n (i + 1) y) ∈ S from ⟨hx, hy⟩),
            Set.indicator_of_mem (show y ∈ {y | t ≤ Ssum n (i + 1) x + Tsum n (i + 1) y} from hy)]
        · rw [Set.indicator_of_notMem (fun h : (x, Tsum n (i + 1) y) ∈ S => hy h.2),
            Set.indicator_of_notMem (show y ∉ {y | t ≤ Ssum n (i + 1) x + Tsum n (i + 1) y} from hy)]
      simp_rw [this]
      rw [measureReal_ind P _ (measurableSet_le measurable_const
        ((measurable_Tsum (i + 1)).const_add _))]
      rfl
    · rw [Set.indicator_of_notMem hx]
      have : ∀ y, Set.indicator S (fun _ => (1:ℝ)) (x, Tsum n (i + 1) y) = 0 := by
        intro y
        rw [Set.indicator_of_notMem (fun h : (x, Tsum n (i + 1) y) ∈ S => hx h.1)]
      simp [this]
  rw [eL] at hdec
  simp_rw [eR] at hdec
  rw [hdec]
  have hmeas : Measurable (Set.indicator (Ev P q t i)
      (fun x => Gf P t (i + 1) (Ssum n (i + 1) x))) :=
    ((measurable_Gf P t (i + 1)).comp (measurable_Ssum (i + 1))).indicator (measurableSet_Ev P q t i)
  have hfi : Integrable (Set.indicator (Ev P q t i)
      (fun x => Gf P t (i + 1) (Ssum n (i + 1) x))) (priorLaw P) := by
    refine integrable_of_bdd P hmeas (B := 1) fun x => ?_
    by_cases hx : x ∈ Ev P q t i
    · rw [Set.indicator_of_mem hx, Real.norm_eq_abs]
      have h0 : 0 ≤ Gf P t (i + 1) (Ssum n (i + 1) x) := measureReal_nonneg
      have h1 : Gf P t (i + 1) (Ssum n (i + 1) x) ≤ 1 := measureReal_le_one
      rw [abs_of_nonneg h0]; exact h1
    · rw [Set.indicator_of_notMem hx]; simp
  have hlow : ∫ x, Set.indicator (Ev P q t i) (fun _ => q / 3) x ∂priorLaw P ≤
      ∫ x, Set.indicator (Ev P q t i) (fun x => Gf P t (i + 1) (Ssum n (i + 1) x)) x ∂priorLaw P := by
    refine integral_mono ((integrable_const _).indicator (measurableSet_Ev P q t i)) hfi fun x => ?_
    by_cases hx : x ∈ Ev P q t i
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; exact Ev_ge P q t hx
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  refine le_trans (le_of_eq ?_) hlow
  rw [integral_indicator (measurableSet_Ev P q t i)]
  simp [mul_comm]

end PersuasionByParts.Known.Dev.Cap
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
noncomputable section

namespace PersuasionByParts.Known.Dev.Cap
open PersuasionByParts.Known

variable {n : ℕ} (P : Prior n)

theorem C_le (h : Fin n → ℝ) (i : Fin n) (x : Fin n → ℝ) :
    ∑ j, min (x j) (h j) ≤ Ssum n i.val x + h i + Tsum n (i.val + 1) x := by
  have e : Ssum n i.val x + h i + Tsum n (i.val + 1) x =
      ∑ j : Fin n, ((if j.val < i.val then x j else 0) + (if j = i then h i else 0) +
        (if i.val + 1 ≤ j.val then x j else 0)) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    unfold Ssum Tsum
    simp
  rw [e]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases h1 : j = i
  · subst h1; simp [min_le_right]
  · have h2 : j.val ≠ i.val := fun hh => h1 (Fin.ext hh)
    by_cases h3 : j.val < i.val
    · simp [h1, h3, not_le.2 (by omega : j.val < i.val + 1), min_le_left]
    · have : i.val + 1 ≤ j.val := by omega
      simp [h1, h3, this, min_le_left]

variable (q t : ℝ)

/-- (F2) for one `i`. -/
theorem F2_one (hq : q ∈ Ioc 0 1) (ht : t ≤ poolMean (sumLaw P) q)
    (h : Fin n → ℝ) (hH1 : ∀ i, (priorLaw P).real {x | t - h i < others i x} ≤ q / 3)
    (i : Fin n) :
    ∫ x, Set.indicator (Ev P q t i.val) (fun x => max (∑ j, min (x j) (h j) - t) 0) x ∂priorLaw P ≤
      9 * Uex P t / q * (priorLaw P).real (Ev P q t i.val) := by
  have hEm := measurableSet_Ev P q t i.val
  set S : Set ((Fin n → ℝ) × ℝ) := {p | p.1 ∈ Ev P q t i.val} with hS
  have hSm : MeasurableSet S := hEm.preimage measurable_fst
  set H : (Fin n → ℝ) → ℝ → ℝ := fun x r =>
    Set.indicator S (fun p => max (Ssum n i.val p.1 + h i + p.2 - t) 0) (x, r) with hHdef
  have hH : Measurable (fun p : (Fin n → ℝ) × ℝ => H p.1 p.2) := by
    refine Measurable.indicator ?_ hSm
    have := measurable_Ssum (n := n) i.val
    fun_prop
  have hdet : ∀ x x' : Fin n → ℝ, (∀ j : Fin n, j.val < i.val + 1 → x j = x' j) → ∀ r,
      H x r = H x' r := by
    intro x x' hxx r
    have h1 := Ev_congr P q t hxx
    have h2 : Ssum n i.val x = Ssum n i.val x' := Ssum_congr _ (fun j hj => hxx j (by omega))
    simp only [hHdef, hS]
    by_cases hx : x ∈ Ev P q t i.val
    · rw [Set.indicator_of_mem (show (x, r) ∈ {p : (Fin n → ℝ) × ℝ | p.1 ∈ Ev P q t i.val} from hx),
        Set.indicator_of_mem (show (x', r) ∈ {p : (Fin n → ℝ) × ℝ | p.1 ∈ Ev P q t i.val} from h1.1 hx)]
      simp only [h2]
    · rw [Set.indicator_of_notMem (show (x, r) ∉ {p : (Fin n → ℝ) × ℝ | p.1 ∈ Ev P q t i.val} from hx),
        Set.indicator_of_notMem (show (x', r) ∉ {p : (Fin n → ℝ) × ℝ | p.1 ∈ Ev P q t i.val} from
          fun h' => hx (h1.2 h'))]
  have hL : Integrable (fun x : Fin n → ℝ => max (Ssum n i.val x + h i + Tsum n (i.val + 1) x - t) 0)
      (priorLaw P) :=
    ((((integrable_Ssum P i.val).add (integrable_const (h i))).add (integrable_Tsum P (i.val + 1))).sub
      (integrable_const t)).pos_part
  have hpt : ∀ x, H x (Tsum n (i.val + 1) x) = Set.indicator (Ev P q t i.val)
      (fun x => max (Ssum n i.val x + h i + Tsum n (i.val + 1) x - t) 0) x := by
    intro x
    by_cases hx : x ∈ Ev P q t i.val
    · simp only [hHdef, hS]
      rw [Set.indicator_of_mem (show (x, Tsum n (i.val + 1) x) ∈
        {p : (Fin n → ℝ) × ℝ | p.1 ∈ Ev P q t i.val} from hx), Set.indicator_of_mem hx]
    · simp only [hHdef, hS]
      rw [Set.indicator_of_notMem (show (x, Tsum n (i.val + 1) x) ∉
        {p : (Fin n → ℝ) × ℝ | p.1 ∈ Ev P q t i.val} from hx), Set.indicator_of_notMem hx]
  have hint : Integrable (fun x => H x (Tsum n (i.val + 1) x)) (priorLaw P) := by
    simp_rw [hpt]; exact hL.indicator hEm
  have hdec := decouple P (i.val + 1) hH hdet hint
  simp_rw [hpt] at hdec
  have eR : ∀ x, ∫ y, H x (Tsum n (i.val + 1) y) ∂priorLaw P =
      Set.indicator (Ev P q t i.val) (fun x => phi P t (i.val + 1) (Ssum n i.val x + h i)) x := by
    intro x
    by_cases hx : x ∈ Ev P q t i.val
    · rw [Set.indicator_of_mem hx]
      simp only [hHdef, hS]
      simp_rw [Set.indicator_of_mem (show (x, _) ∈
        {p : (Fin n → ℝ) × ℝ | p.1 ∈ Ev P q t i.val} from hx)]
      rfl
    · rw [Set.indicator_of_notMem hx]
      simp only [hHdef, hS]
      simp_rw [Set.indicator_of_notMem (show (x, _) ∉
        {p : (Fin n → ℝ) × ℝ | p.1 ∈ Ev P q t i.val} from hx)]
      simp
  simp_rw [eR] at hdec
  have hU0 := Uex_nonneg P t
  have hq0 := hq.1
  -- first inequality: C ≤ ...
  have hC : Integrable (fun x : Fin n → ℝ => max (∑ j, min (x j) (h j) - t) 0) (priorLaw P) :=
    ((integrable_C P h).sub (integrable_const t)).pos_part
  have step1 : ∫ x, Set.indicator (Ev P q t i.val) (fun x => max (∑ j, min (x j) (h j) - t) 0) x
      ∂priorLaw P ≤ ∫ x, Set.indicator (Ev P q t i.val)
        (fun x => max (Ssum n i.val x + h i + Tsum n (i.val + 1) x - t) 0) x ∂priorLaw P := by
    refine integral_mono (hC.indicator hEm) (hL.indicator hEm) fun x => ?_
    by_cases hx : x ∈ Ev P q t i.val
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      exact max_le_max (by linarith [C_le h i x]) le_rfl
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  refine le_trans step1 (le_of_eq_of_le hdec ?_)
  have hphim : Measurable (Set.indicator (Ev P q t i.val)
      (fun x => phi P t (i.val + 1) (Ssum n i.val x + h i))) :=
    ((measurable_phi P t (i.val + 1)).comp ((measurable_Ssum (n := n) i.val).add_const _)).indicator hEm
  have hphii : Integrable (Set.indicator (Ev P q t i.val)
      (fun x => phi P t (i.val + 1) (Ssum n i.val x + h i))) (priorLaw P) := by
    refine integrable_of_bdd P hphim (B := 9 * Uex P t / q) fun x => ?_
    by_cases hx : x ∈ Ev P q t i.val
    · rw [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_of_nonneg (phi_nonneg P t _ _)]
      exact phi_bound P q t hq ht h hH1 i _ (Ev_lt P q t hx)
    · rw [Set.indicator_of_notMem hx]; simp; positivity
  have : ∫ x, Set.indicator (Ev P q t i.val)
      (fun x => phi P t (i.val + 1) (Ssum n i.val x + h i)) x ∂priorLaw P ≤
      ∫ x, Set.indicator (Ev P q t i.val) (fun _ => 9 * Uex P t / q) x ∂priorLaw P := by
    refine integral_mono hphii ((integrable_const _).indicator hEm) fun x => ?_
    by_cases hx : x ∈ Ev P q t i.val
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      exact phi_bound P q t hq ht h hH1 i _ (Ev_lt P q t hx)
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
  refine le_trans this (le_of_eq ?_)
  rw [integral_indicator hEm]
  simp [mul_comm]

end PersuasionByParts.Known.Dev.Cap
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter
noncomputable section

namespace PersuasionByParts.Known.Dev.Cap
open PersuasionByParts.Known

variable {n : ℕ} (P : Prior n)

/-- Step 3: core term. -/
theorem core_term (_hn : 0 < n) (q t : ℝ) (hq : q ∈ Ioc 0 1) (ht : t ≤ poolMean (sumLaw P) q)
    (hp : revelationProbability P t < q / 3) :
    ∫ x, max (∑ i, min (x i) (target P q t i) - t) 0 ∂priorLaw P ≤
      27 * Uex P t * revelationProbability P t / q ^ 2 := by
  set h : Fin n → ℝ := target P q t with hh
  have hH1 : ∀ i, (priorLaw P).real {x | t - h i < others i x} ≤ q / 3 :=
    fun i => others_tail P q t hq i
  have hq0 := hq.1
  have hU0 := Uex_nonneg P t
  have hEm := measurableSet_Ev P q t
  have hX : MeasurableSet {x : Fin n → ℝ | t ≤ total x} :=
    measurableSet_le measurable_const measurable_total
  have hC : Integrable (fun x : Fin n → ℝ => max (∑ j, min (x j) (h j) - t) 0) (priorLaw P) :=
    ((integrable_C P h).sub (integrable_const t)).pos_part
  -- pointwise cover
  have hpt : ∀ x : Fin n → ℝ, max (∑ j, min (x j) (h j) - t) 0 ≤
      ∑ i : Fin n, Set.indicator (Ev P q t i.val) (fun x => max (∑ j, min (x j) (h j) - t) 0) x := by
    intro x
    have hnn : ∀ i : Fin n, 0 ≤ Set.indicator (Ev P q t i.val)
        (fun x => max (∑ j, min (x j) (h j) - t) 0) x :=
      fun i => Set.indicator_nonneg (fun _ _ => le_max_right _ _) x
    by_cases hc : ∑ j, min (x j) (h j) - t ≤ 0
    · rw [max_eq_right hc]; exact Finset.sum_nonneg fun i _ => hnn i
    · have hc0 : 0 < ∑ j, min (x j) (h j) - t := not_le.1 hc
      have hCx : ∑ j, min (x j) (h j) ≤ total x := Finset.sum_le_sum fun j _ => min_le_left _ _
      have htx : t ≤ total x := by linarith
      obtain ⟨i, hi⟩ := Ev_cover P q t hq hp htx
      calc max (∑ j, min (x j) (h j) - t) 0
          = Set.indicator (Ev P q t i.val) (fun x => max (∑ j, min (x j) (h j) - t) 0) x := by
            rw [Set.indicator_of_mem hi]
        _ ≤ _ := Finset.single_le_sum (f := fun i : Fin n => Set.indicator (Ev P q t i.val)
            (fun x => max (∑ j, min (x j) (h j) - t) 0) x) (fun i _ => hnn i) (Finset.mem_univ i)
  have hint : ∀ i : Fin n, Integrable (Set.indicator (Ev P q t i.val)
      (fun x => max (∑ j, min (x j) (h j) - t) 0)) (priorLaw P) := fun i => hC.indicator (hEm _)
  have s1 : ∫ x, max (∑ j, min (x j) (h j) - t) 0 ∂priorLaw P ≤
      ∑ i : Fin n, ∫ x, Set.indicator (Ev P q t i.val)
        (fun x => max (∑ j, min (x j) (h j) - t) 0) x ∂priorLaw P := by
    rw [← integral_finsetSum _ (fun i _ => hint i)]
    exact integral_mono hC (integrable_finsetSum _ fun i _ => hint i) hpt
  have s2 : ∑ i : Fin n, ∫ x, Set.indicator (Ev P q t i.val)
        (fun x => max (∑ j, min (x j) (h j) - t) 0) x ∂priorLaw P ≤
      ∑ i : Fin n, 9 * Uex P t / q * (priorLaw P).real (Ev P q t i.val) :=
    Finset.sum_le_sum fun i _ => F2_one P q t hq ht h hH1 i
  -- sum of probabilities
  have s3 : q / 3 * ∑ i : Fin n, (priorLaw P).real (Ev P q t i.val) ≤ revelationProbability P t := by
    rw [Finset.mul_sum]
    refine le_trans (Finset.sum_le_sum fun i _ => F1_one P q t i.val) ?_
    have hdisj : Pairwise (Function.onFun Disjoint
        (fun i : Fin n => Ev P q t i.val ∩ {x : Fin n → ℝ | t ≤ total x})) := by
      intro i j hij
      rw [Function.onFun, Set.disjoint_left]
      intro x hxi hxj
      exact hij (Fin.ext (Ev_disj P q t hxi.1 hxj.1))
    rw [← measureReal_iUnion_fintype hdisj (fun i => (hEm _).inter hX)]
    exact measureReal_mono (Set.iUnion_subset fun i => Set.inter_subset_right)
  have s4 : ∑ i : Fin n, (priorLaw P).real (Ev P q t i.val) ≤ 3 * revelationProbability P t / q := by
    rw [le_div_iff₀ hq0]; linarith
  have hcoef : 0 ≤ 9 * Uex P t / q := by positivity
  calc ∫ x, max (∑ j, min (x j) (h j) - t) 0 ∂priorLaw P
      ≤ ∑ i : Fin n, 9 * Uex P t / q * (priorLaw P).real (Ev P q t i.val) := le_trans s1 s2
    _ = 9 * Uex P t / q * ∑ i : Fin n, (priorLaw P).real (Ev P q t i.val) := by rw [Finset.mul_sum]
    _ ≤ 9 * Uex P t / q * (3 * revelationProbability P t / q) := mul_le_mul_of_nonneg_left s4 hcoef
    _ = 27 * Uex P t * revelationProbability P t / q ^ 2 := by field_simp; ring

end PersuasionByParts.Known.Dev.Cap
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
noncomputable section

namespace PersuasionByParts.Known

/-- Lemma 2.3, printed p. 8 / PDF p. 9, with the standing hypotheses on p. 7. -/
theorem chk_capacity_lemma {n : ℕ} (P : Prior n) (hn : 0 < n)
    (q t : ℝ) (hq : q ∈ Ioc 0 1) (ht : t ≤ poolMean (sumLaw P) q) :
    totalCapacity P q t + 18 * revelationProbability P t / q ≥ 2 * q / 3 ∧
    (totalCapacity P q t < q / 6 → revelationProbability P t > q ^ 2 / 36) := by
  have hq0 : 0 < q := hq.1
  have hq1 : q ≤ 1 := hq.2
  have key : totalCapacity P q t + 18 * revelationProbability P t / q ≥ 2 * q / 3 := by
    by_contra hcon
    push Not at hcon
    have hp0 : 0 ≤ revelationProbability P t := measureReal_nonneg
    have hB0 : 0 ≤ totalCapacity P q t := by
      unfold totalCapacity coordinateCapacity
      exact Finset.sum_nonneg fun i _ =>
        (Dev.Cap.coordinateCapacity_nonneg P q t i)
    have hp : revelationProbability P t < q / 3 := by
      have h1 : 18 * revelationProbability P t / q < 2 * q / 3 := by linarith
      rw [div_lt_iff₀ hq0] at h1
      nlinarith
    have hB : totalCapacity P q t < 2 * q / 3 := by
      have : 0 ≤ 18 * revelationProbability P t / q := by positivity
      linarith
    have hU := Dev.Cap.Uex_pos P q t hq ht hp
    have h1 := Dev.Cap.Uex_le P q t
    have h2 : ∑ i, (∫ x, max (x - target P q t i) 0 ∂(P.marginal i)) ≤
        ∑ i, coordinateCapacity P q t i * (3 * Dev.Cap.Uex P t / (2 * q)) :=
      Finset.sum_le_sum fun i _ => Dev.Cap.tail_term P hn q t hq ht hB i
    rw [← Finset.sum_mul] at h2
    have h3 := Dev.Cap.core_term P hn q t hq ht hp
    have h4 : Dev.Cap.Uex P t ≤ totalCapacity P q t * (3 * Dev.Cap.Uex P t / (2 * q)) +
        27 * Dev.Cap.Uex P t * revelationProbability P t / q ^ 2 := by
      unfold totalCapacity; linarith
    have h5 : 1 ≤ totalCapacity P q t * (3 / (2 * q)) + 27 * revelationProbability P t / q ^ 2 := by
      have : Dev.Cap.Uex P t * 1 ≤ Dev.Cap.Uex P t *
          (totalCapacity P q t * (3 / (2 * q)) + 27 * revelationProbability P t / q ^ 2) := by
        calc Dev.Cap.Uex P t * 1 = Dev.Cap.Uex P t := mul_one _
          _ ≤ _ := by convert h4 using 1; field_simp
      exact le_of_mul_le_mul_left this hU
    have h6 : 2 * q / 3 ≤ totalCapacity P q t + 18 * revelationProbability P t / q := by
      have h7 := mul_le_mul_of_nonneg_left h5 (by positivity : (0:ℝ) ≤ 2 * q / 3)
      have : 2 * q / 3 * (totalCapacity P q t * (3 / (2 * q)) + 27 * revelationProbability P t / q ^ 2)
          = totalCapacity P q t + 18 * revelationProbability P t / q := by
        field_simp; ring
      linarith
    linarith
  refine ⟨key, fun hB => ?_⟩
  have h1 : 2 * q / 3 ≤ totalCapacity P q t + 18 * revelationProbability P t / q := key
  have h2 : q / 2 < 18 * revelationProbability P t / q := by linarith
  rw [lt_div_iff₀ hq0] at h2
  show q ^ 2 / 36 < revelationProbability P t
  nlinarith

end PersuasionByParts.Known

end
end

theorem solution : type_of% @PersuasionByParts.Known.chk_capacity_lemma := @PersuasionByParts.Known.chk_capacity_lemma
