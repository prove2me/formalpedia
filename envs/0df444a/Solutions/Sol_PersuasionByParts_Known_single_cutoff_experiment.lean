-- Prove2me | solution 1 for PersuasionByParts.Known.single_cutoff_experiment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T16:55:06.536106+00:00
-- url     : https://prove2.me/submissions/1b4e8c01-34ce-4653-88be-595bc74808c8

import Theorems.Thm_PersuasionByParts_Known_pooling_semantics
import Theorems.Thm_PersuasionByParts_Known_capacity_lemma
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

/-- A function with the right set integrals is the posterior mean, almost surely. -/
theorem ae_eq_posterior_integral (f : Ω → ℝ) (hfm : Measurable f) (hf : Integrable f μ)
    (m : 𝓧 → ℝ) (hm : Integrable m (κ ∘ₘ μ))
    (h : ∀ B : Set 𝓧, MeasurableSet B →
      ∫ s in B, m s ∂(κ ∘ₘ μ) = ∫ x, f x * (κ x).real B ∂μ) :
    m =ᵐ[κ ∘ₘ μ] fun s => ∫ x, f x ∂(κ†μ) s := by
  refine hm.ae_eq_of_forall_setIntegral_eq _ _ (integrable_posterior_integral κ μ f hfm hf)
    fun B hB _ => ?_
  rw [h B hB, setIntegral_posterior κ μ f hfm hf hB]

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

end PersuasionByParts.Known.Dev.PS

namespace PersuasionByParts.Known

/-- Section 1.1, unnumbered top-pool definition and mean identity, printed p. 3.
The mean at a zero-mass pool is never asserted to be a conditional mean. -/
theorem chk_pooling_semantics (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) (s : ℝ) (hs : s ∈ Icc 0 1) :
    (∀ z : ℝ, topSelector μ s z ∈ Icc 0 1) ∧
    (∫ z, topSelector μ s z ∂μ) = s ∧
    (∫ z, topSelector μ s z * z ∂μ) = s * poolMean μ s ∧
    (poolKernel μ s ∘ₘ μ).real {Sum.inl ()} = s ∧
    (0 < s → PersuasionNetworks.posteriorMean μ (poolKernel μ s) (Sum.inl ()) =
      poolMean μ s) :=
  by
  try haveI := μ; try haveI := hμ; try haveI := s; try haveI := hs; first
    | exact PersuasionByParts.Known.pooling_semantics μ hμ s hs
    | exact PersuasionByParts.Known.pooling_semantics
    | exact PersuasionByParts.Known.pooling_semantics ..
    | (apply PersuasionByParts.Known.pooling_semantics <;> first | assumption | infer_instance)
    | simpa using PersuasionByParts.Known.pooling_semantics

end PersuasionByParts.Known
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
noncomputable section

namespace PersuasionByParts.Known.Dev.Single
open PersuasionByParts.Known

theorem unif_Iio {a : ℝ} (ha : a ∈ Icc (0:ℝ) 1) : privateUniform (Iio a) = ENNReal.ofReal a := by
  unfold privateUniform
  rw [Measure.restrict_apply measurableSet_Iio]
  have h2 : Iio a ∩ Icc (0:ℝ) 1 = Ico 0 a := by
    ext u
    simp only [mem_inter_iff, mem_Iio, mem_Icc, mem_Ico]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩; exact ⟨h1, h2, by linarith [ha.2]⟩
  rw [h2, Real.volume_Ico]; simp

theorem unif_real_Iio {a : ℝ} (ha : a ∈ Icc (0:ℝ) 1) : privateUniform.real (Iio a) = a := by
  rw [measureReal_def, unif_Iio ha, ENNReal.toReal_ofReal ha.1]

theorem poolKernel_eq (μ : Measure ℝ) (s x : ℝ) :
    poolKernel μ s x = privateUniform.map (fun u => poolReport μ s (x, u)) := by
  unfold poolKernel
  rw [Kernel.deterministic_comp_eq_map, Kernel.map_apply _ (measurable_poolReport μ s),
    Kernel.prod_apply, Kernel.id_apply, Kernel.const_apply, Measure.dirac_prod,
    Measure.map_map (measurable_poolReport μ s) measurable_prodMk_left]
  rfl

theorem comp_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] (s : ℝ) :
    poolKernel μ s ∘ₘ μ = (μ.prod privateUniform).map (poolReport μ s) := by
  ext B hB
  rw [Measure.bind_apply hB (poolKernel μ s).aemeasurable,
    Measure.map_apply (measurable_poolReport μ s) hB,
    Measure.prod_apply (measurable_poolReport μ s hB)]
  refine lintegral_congr fun x => ?_
  rw [poolKernel_eq, Measure.map_apply (by have := measurable_poolReport μ s; fun_prop) hB]
  rfl

/-- the explicit posterior value -/
def val (c : ℝ) : Unit ⊕ ℝ → ℝ := Sum.elim (fun _ => c) id

theorem measurable_val (c : ℝ) : Measurable (val c) :=
  Measurable.sumElim measurable_const measurable_id

theorem integrable_fst {μ : Measure ℝ} [IsProbabilityMeasure μ] (hμ : Integrable id μ) :
    Integrable (fun z : ℝ × ℝ => z.1) (μ.prod privateUniform) :=
  hμ.comp_fst privateUniform

theorem post_ae (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : Integrable id μ) {s : ℝ}
    (hs : s ∈ Icc (0:ℝ) 1) :
    (fun σ => PersuasionNetworks.posteriorMean μ (poolKernel μ s) σ)
      =ᵐ[poolKernel μ s ∘ₘ μ] val (poolMean μ s) := by
  classical
  have := Dev.PS.msc
  obtain ⟨hmem, hint, hmom⟩ := Dev.Pool.top_spec μ hμ hs
  set c := poolMean μ s with hc
  set r := poolReport μ s with hr
  set K := μ.prod privateUniform with hK
  have hrm : Measurable r := measurable_poolReport μ s
  have hρ : poolKernel μ s ∘ₘ μ = K.map r := comp_eq μ s
  -- integrability of val over rho
  have hvalint : Integrable (val c) (poolKernel μ s ∘ₘ μ) := by
    rw [hρ, integrable_map_measure (measurable_val c).aestronglyMeasurable hrm.aemeasurable]
    have hmeas : Measurable (val c ∘ r) := (measurable_val c).comp hrm
    refine ((integrable_fst hμ).norm.add (integrable_const |c|)).mono'
      hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun z => ?_)
    simp only [Function.comp, hr, poolReport, Pi.add_apply, Real.norm_eq_abs]
    split_ifs <;> simp [val] <;> linarith [abs_nonneg c, abs_nonneg z.1]
  have htm : Measurable (topSelector μ s) := measurable_topSelector μ s
  have hint1 : Integrable (topSelector μ s) μ :=
    (integrable_const (1:ℝ)).mono' htm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        have := hmem x
        rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2)
  have hint2 : Integrable (fun x => topSelector μ s x * x) μ := by
    refine hμ.norm.mono' (htm.mul measurable_id).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    have := hmem x
    simp only [Real.norm_eq_abs, abs_mul, id]
    rw [abs_of_nonneg this.1]
    nlinarith [abs_nonneg x, this.2]
  refine (Dev.Post.ae_eq_posterior_integral (poolKernel μ s) μ (fun x => x) measurable_id hμ
    (val c) hvalint ?_).symm
  intro B hB
  have step1 : ∫ s in B, val c s ∂(poolKernel μ s ∘ₘ μ) = ∫ z, B.indicator (val c) (r z) ∂K := by
    rw [← integral_indicator hB, hρ,
      integral_map hrm.aemeasurable ((measurable_val c).indicator hB).aestronglyMeasurable]
  have hrB : MeasurableSet (r ⁻¹' B) := hrm hB
  have step2 : ∀ x, (poolKernel μ s x).real B =
      ∫ u, (r ⁻¹' B).indicator (fun _ => (1:ℝ)) (x, u) ∂privateUniform := by
    intro x
    have hmx : MeasurableSet (Prod.mk x ⁻¹' (r ⁻¹' B)) := measurable_prodMk_left hrB
    have : (fun u => (r ⁻¹' B).indicator (fun _ => (1:ℝ)) (x, u)) =
        (Prod.mk x ⁻¹' (r ⁻¹' B)).indicator (fun _ => 1) := by
      ext u; rfl
    rw [this, integral_indicator_const _ hmx, poolKernel_eq, measureReal_def,
      Measure.map_apply (f := fun u => poolReport μ s (x, u))
        ((measurable_poolReport μ s).comp measurable_prodMk_left) hB]
    simp only [measureReal_def, smul_eq_mul, mul_one]
    rfl
  have hG : Measurable (fun z : ℝ × ℝ => (r ⁻¹' B).indicator (fun _ => (1:ℝ)) z) :=
    measurable_const.indicator hrB
  have hGi : Integrable (fun z : ℝ × ℝ => z.1 * (r ⁻¹' B).indicator (fun _ => (1:ℝ)) z) K := by
    refine (integrable_fst hμ).norm.mono' (measurable_fst.mul hG).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => ?_)
    simp only [Real.norm_eq_abs, abs_mul]
    by_cases h : z ∈ r ⁻¹' B <;> simp [h]
  have step3 : ∫ x, x * (poolKernel μ s x).real B ∂μ =
      ∫ z, z.1 * (r ⁻¹' B).indicator (fun _ => (1:ℝ)) z ∂K := by
    rw [hK, integral_prod _ (hK ▸ hGi)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [step2, integral_const_mul]
  have hFi : Integrable (fun z => B.indicator (val c) (r z)) K := by
    have := hvalint.indicator hB
    rw [hρ, integrable_map_measure this.aestronglyMeasurable hrm.aemeasurable] at this
    exact this
  -- pointwise difference
  set H : ℝ × ℝ → ℝ := fun z => (if Sum.inl () ∈ B then (1:ℝ) else 0) *
    (if z.2 < topSelector μ s z.1 then c - z.1 else 0) with hH
  have hpt : ∀ z : ℝ × ℝ, B.indicator (val c) (r z) -
      z.1 * (r ⁻¹' B).indicator (fun _ => (1:ℝ)) z = H z := by
    intro z
    by_cases hz : z.2 < topSelector μ s z.1
    · have : r z = Sum.inl () := by simp [hr, poolReport, hz]
      by_cases hb : (Sum.inl () : Unit ⊕ ℝ) ∈ B <;> simp [hH, hz, this, hb, val, indicator]
    · have : r z = Sum.inr z.1 := by simp [hr, poolReport, hz]
      by_cases hb : (Sum.inr z.1 : Unit ⊕ ℝ) ∈ B <;> simp [hH, hz, this, hb, val, indicator]
  have hdiff : ∫ z, H z ∂K = 0 := by
    have hHm : ∀ x : ℝ, ∫ u, H (x, u) ∂privateUniform =
        (if Sum.inl () ∈ B then (1:ℝ) else 0) * ((c - x) * topSelector μ s x) := by
      intro x
      have hm : MeasurableSet (Iio (topSelector μ s x)) := measurableSet_Iio
      have : (fun u => H (x, u)) =
          (fun u => (if Sum.inl () ∈ B then (1:ℝ) else 0) *
            (Iio (topSelector μ s x)).indicator (fun _ => c - x) u) := by
        ext u; simp [hH, indicator]
      rw [this, integral_const_mul, integral_indicator_const _ hm, unif_real_Iio (hmem x)]
      simp [mul_comm]
    have hHi : Integrable H K := by
      have := (hFi.sub hGi)
      refine this.congr (Filter.Eventually.of_forall fun z => ?_)
      exact hpt z
    rw [hK, integral_prod _ (hK ▸ hHi)]
    simp_rw [hHm]
    rw [integral_const_mul]
    have : ∫ x, (c - x) * topSelector μ s x ∂μ = 0 := by
      have e : ∀ x : ℝ, (c - x) * topSelector μ s x = c * topSelector μ s x - topSelector μ s x * x := by
        intro x; ring
      simp_rw [e]
      rw [integral_sub (hint1.const_mul c) hint2, integral_const_mul, hint, hmom]
      ring
    rw [this, mul_zero]
  have : ∫ z, B.indicator (val c) (r z) ∂K = ∫ z, z.1 * (r ⁻¹' B).indicator (fun _ => (1:ℝ)) z ∂K := by
    have h2 := integral_sub hFi hGi
    simp_rw [hpt] at h2
    rw [hdiff] at h2
    linarith
  rw [step1, step3, this]

end PersuasionByParts.Known.Dev.Single
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
noncomputable section

namespace PersuasionByParts.Known.Dev.Single
open PersuasionByParts.Known
open scoped Classical

variable {n : ℕ} (P : Prior n) (s : Fin n → ℝ)

/-- the coupling space: for each coordinate, a value and a private uniform seed -/
def nu : Measure (Fin n → ℝ × ℝ) :=
  Measure.pi (fun i => (P.marginal i).prod privateUniform)

instance : IsProbabilityMeasure (nu P) := by unfold nu; infer_instance

def fmap (w : Fin n → ℝ × ℝ) : Fin n → Unit ⊕ ℝ :=
  fun i => poolReport (P.marginal i) (s i) (w i)

def poolSet (i : Fin n) : Set (Fin n → ℝ × ℝ) :=
  {w | (w i).2 < topSelector (P.marginal i) (s i) (w i).1}

theorem measurable_fmap : Measurable (fmap P s) :=
  measurable_pi_iff.2 fun i => (measurable_poolReport _ _).comp (measurable_pi_apply i)

theorem measurableSet_poolSet (i : Fin n) : MeasurableSet (poolSet P s i) :=
  measurableSet_lt (measurable_snd.comp (measurable_pi_apply i))
    ((measurable_topSelector _ _).comp (measurable_fst.comp (measurable_pi_apply i)))

theorem law_eq :
    Measure.pi (fun i => poolKernel (P.marginal i) (s i) ∘ₘ P.marginal i) =
      (nu P).map (fmap P s) := by
  unfold nu fmap
  rw [Measure.pi_map_pi (fun i => (measurable_poolReport _ _).aemeasurable)]
  congr 1
  ext1 i
  exact comp_eq _ _

theorem nu_pool (hs : ∀ i, s i ∈ Icc (0:ℝ) 1) (i : Fin n) :
    (nu P).real (poolSet P s i) = s i := by
  have h1 : (nu P).map (fun w => w i) = (P.marginal i).prod privateUniform := by
    unfold nu
    exact (measurePreserving_eval _ i).map_eq
  have hset : poolSet P s i = (fun w : Fin n → ℝ × ℝ => w i) ⁻¹'
      (poolReport (P.marginal i) (s i) ⁻¹' {Sum.inl ()}) := by
    ext w; simp [poolSet, poolReport]
  have hmsc := Dev.PS.msc
  have hm : MeasurableSet (poolReport (P.marginal i) (s i) ⁻¹' {Sum.inl ()}) :=
    measurable_poolReport _ _ (measurableSet_singleton _)
  rw [hset, measureReal_def, ← Measure.map_apply (measurable_pi_apply i) hm, h1,
    ← Measure.map_apply (measurable_poolReport _ _) (measurableSet_singleton _), ← comp_eq]
  have := (chk_pooling_semantics (P.marginal i) (P.finiteMean i) (s i) (hs i)).2.2.2.1
  rw [← measureReal_def]; exact this

theorem ae_post (hs : ∀ i, s i ∈ Icc (0:ℝ) 1) :
    ∀ᵐ w ∂(nu P), ∑ i, PersuasionNetworks.posteriorMean (P.marginal i)
        (poolKernel (P.marginal i) (s i)) (fmap P s w i) =
      ∑ i, if w ∈ poolSet P s i then poolMean (P.marginal i) (s i) else (w i).1 := by
  have h1 : ∀ᵐ σ ∂(Measure.pi (fun i => poolKernel (P.marginal i) (s i) ∘ₘ P.marginal i)),
      ∀ i, PersuasionNetworks.posteriorMean (P.marginal i) (poolKernel (P.marginal i) (s i)) (σ i) =
        val (poolMean (P.marginal i) (s i)) (σ i) := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_eval (fun i => poolKernel (P.marginal i) (s i) ∘ₘ P.marginal i) i
      |>.quasiMeasurePreserving.ae (post_ae (P.marginal i) (P.finiteMean i) (hs i)))
  rw [law_eq] at h1
  have h2 := ae_of_ae_map (measurable_fmap P s).aemeasurable h1
  filter_upwards [h2] with w hw
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hw i]
  by_cases h : w ∈ poolSet P s i
  · have : fmap P s w i = Sum.inl () := by simp [fmap, poolReport]; exact h
    simp [this, h, val]
  · have : fmap P s w i = Sum.inr (w i).1 := by
      have h' : ¬ (w i).2 < topSelector (P.marginal i) (s i) (w i).1 := h
      simp [fmap, poolReport, h']
    simp [this, h, val]

theorem count_eq (w : Fin n → ℝ × ℝ) :
    poolCount (fmap P s w) = ∑ i, if w ∈ poolSet P s i then (1:ℝ) else 0 := by
  unfold poolCount
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : w ∈ poolSet P s i
  · have : fmap P s w i = Sum.inl () := by simp [fmap, poolReport]; exact h
    simp [this, h]
  · have : fmap P s w i = Sum.inr (w i).1 := by
      have h' : ¬ (w i).2 < topSelector (P.marginal i) (s i) (w i).1 := h
      simp [fmap, poolReport, h']
    simp [this, h]

theorem law_x : (nu P).map (fun w i => (w i).1) = priorLaw P := by
  unfold nu priorLaw
  rw [Measure.pi_map_pi (f := fun i (z : ℝ × ℝ) => z.1) (fun i => measurable_fst.aemeasurable)]
  congr 1
  ext1 i
  simp

end PersuasionByParts.Known.Dev.Single
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

end PersuasionByParts.Known.Dev.CapExtra
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
noncomputable section

namespace PersuasionByParts.Known.Dev.Cap
open PersuasionByParts.Known

variable {n : ℕ} (P : Prior n)

theorem measurable_total : Measurable (total : (Fin n → ℝ) → ℝ) := by
  unfold total; fun_prop

theorem measurable_others (i : Fin n) : Measurable (others i : (Fin n → ℝ) → ℝ) := by
  unfold others; fun_prop

instance : IsProbabilityMeasure (sumLaw P) := by
  unfold sumLaw
  exact Measure.isProbabilityMeasure_map measurable_total.aemeasurable

instance (i : Fin n) : IsProbabilityMeasure (othersLaw P i) := by
  unfold othersLaw
  exact Measure.isProbabilityMeasure_map (measurable_others i).aemeasurable

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

variable (q t : ℝ)

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

variable (q t : ℝ)

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

variable (q t : ℝ)

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
    (totalCapacity P q t < q / 6 → revelationProbability P t > q ^ 2 / 36) :=
  by
  try haveI := P; try haveI := hn; try haveI := q; try haveI := t; try haveI := hq; try haveI := ht; first
    | exact PersuasionByParts.Known.capacity_lemma P hn q t hq ht
    | exact PersuasionByParts.Known.capacity_lemma
    | exact PersuasionByParts.Known.capacity_lemma ..
    | (apply PersuasionByParts.Known.capacity_lemma <;> first | assumption | infer_instance)
    | simpa using PersuasionByParts.Known.capacity_lemma

end PersuasionByParts.Known

end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
noncomputable section

namespace PersuasionByParts.Known.Dev.Single
open PersuasionByParts.Known
open scoped Classical

variable {n : ℕ} (P : Prior n) (s : Fin n → ℝ)

/-- others reveal, and their revealed sum is at least `c` -/
def Rset (i : Fin n) (c : ℝ) : Set (Fin n → ℝ × ℝ) :=
  {w | (∀ j, j ≠ i → w ∉ poolSet P s j) ∧ c ≤ ∑ j ∈ Finset.univ.erase i, (w j).1}

def Gset (i : Fin n) (c : ℝ) : Set (Fin n → ℝ × ℝ) :=
  {w | c ≤ ∑ j ∈ Finset.univ.erase i, (w j).1}

theorem measurableSet_Gset (i : Fin n) (c : ℝ) : MeasurableSet (Gset i c) := by
  unfold Gset
  exact measurableSet_le measurable_const
    (Finset.measurable_sum _ fun j _ => measurable_fst.comp (measurable_pi_apply j))

theorem measurableSet_Rset (i : Fin n) (c : ℝ) : MeasurableSet (Rset P s i c) := by
  unfold Rset
  have hm1 : MeasurableSet {w : Fin n → ℝ × ℝ | ∀ j, j ≠ i → w ∉ poolSet P s j} := by
    have : {w : Fin n → ℝ × ℝ | ∀ j, j ≠ i → w ∉ poolSet P s j} =
        ⋂ j, ⋂ (_ : j ≠ i), (poolSet P s j)ᶜ := by ext w; simp
    rw [this]
    exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      (measurableSet_poolSet P s j).compl
  exact MeasurableSet.inter hm1 (measurableSet_Gset i c)

theorem nu_Gset (i : Fin n) (c : ℝ) :
    (nu P).real (Gset i c) = (priorLaw P).real {x | c ≤ others i x} := by
  have hm : MeasurableSet {x : Fin n → ℝ | c ≤ others i x} :=
    measurableSet_le measurable_const (Dev.Cap.measurable_others i)
  have hset : Gset i c = (fun (w : Fin n → ℝ × ℝ) j => (w j).1) ⁻¹' {x | c ≤ others i x} := by
    ext w; simp [Gset, others]
  rw [hset, measureReal_def, measureReal_def, ← law_x P,
    Measure.map_apply (f := fun (w : Fin n → ℝ × ℝ) j => (w j).1)
      (measurable_pi_iff.2 fun j => measurable_fst.comp (measurable_pi_apply j)) hm]

theorem indep_split (i : Fin n) (c : ℝ) :
    (nu P).real (poolSet P s i ∩ Rset P s i c) =
      (nu P).real (poolSet P s i) * (nu P).real (Rset P s i c) := by
  have hind : iIndepFun (fun (j : Fin n) (w : Fin n → ℝ × ℝ) => w j) (nu P) := by
    have := iIndepFun_pi (μ := fun j => (P.marginal j).prod privateUniform)
      (X := fun _ => (id : ℝ × ℝ → ℝ × ℝ)) (fun _ => aemeasurable_id)
    simpa [nu] using this
  have hdisj : Disjoint ({i} : Finset (Fin n)) (Finset.univ.erase i) := by simp
  have h2 := hind.indepFun_finset {i} (Finset.univ.erase i) hdisj
    (fun j => measurable_pi_apply j)
  have hi : i ∈ ({i} : Finset (Fin n)) := Finset.mem_singleton_self i
  set A : Set ((↥({i} : Finset (Fin n))) → ℝ × ℝ) :=
    {v | (v ⟨i, hi⟩).2 < topSelector (P.marginal i) (s i) (v ⟨i, hi⟩).1} with hA
  set Bs : Set ((↥(Finset.univ.erase i)) → ℝ × ℝ) :=
    {v | (∀ j : (↥(Finset.univ.erase i)),
        ¬ (v j).2 < topSelector (P.marginal j) (s j) (v j).1) ∧
      c ≤ ∑ j : (↥(Finset.univ.erase i)), (v j).1} with hB
  have hAm : MeasurableSet A :=
    measurableSet_lt (measurable_snd.comp (measurable_pi_apply _))
      ((measurable_topSelector _ _).comp (measurable_fst.comp (measurable_pi_apply _)))
  have hBm : MeasurableSet Bs := by
    refine MeasurableSet.inter (?_ : MeasurableSet {v : (↥(Finset.univ.erase i)) → ℝ × ℝ | ∀ j : (↥(Finset.univ.erase i)),
        ¬ (v j).2 < topSelector (P.marginal j) (s j) (v j).1}) ?_
    · have : {v : (↥(Finset.univ.erase i)) → ℝ × ℝ | ∀ j : (↥(Finset.univ.erase i)),
        ¬ (v j).2 < topSelector (P.marginal j) (s j) (v j).1} =
          ⋂ j : (↥(Finset.univ.erase i)),
            {v | (v j).2 < topSelector (P.marginal j) (s j) (v j).1}ᶜ := by ext v; simp
      rw [this]
      exact MeasurableSet.iInter fun j => (measurableSet_lt (measurable_snd.comp (measurable_pi_apply _))
        ((measurable_topSelector _ _).comp (measurable_fst.comp (measurable_pi_apply _)))).compl
    · exact measurableSet_le measurable_const
        (Finset.measurable_sum _ fun j _ => measurable_fst.comp (measurable_pi_apply j))
  have hpre1 : (fun (w : Fin n → ℝ × ℝ) (j : (↥({i} : Finset (Fin n)))) => w j) ⁻¹' A = poolSet P s i := by
    ext w; simp [hA, poolSet]
  have hpre2 : (fun (w : Fin n → ℝ × ℝ) (j : (↥(Finset.univ.erase i))) => w j) ⁻¹' Bs
      = Rset P s i c := by
    ext w
    have e : ∑ j : ↥(Finset.univ.erase i), (w j).1 = ∑ j ∈ Finset.univ.erase i, (w j).1 :=
      Finset.sum_coe_sort (Finset.univ.erase i) (fun j => (w j).1)
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun j hj => h1 ⟨j, by simp [hj]⟩, by rw [← e]; exact h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun j => h1 j (Finset.mem_erase.1 j.2).1, by rw [e]; exact h2⟩
  have := h2.measure_inter_preimage_eq_mul A Bs hAm hBm
  rw [hpre1, hpre2] at this
  rw [measureReal_def, measureReal_def, measureReal_def, this, ENNReal.toReal_mul]

theorem lb (hs : ∀ j, s j ∈ Icc (0:ℝ) 1) (i : Fin n) (c a b : ℝ)
    (hG : a ≤ (priorLaw P).real {x | c ≤ others i x})
    (hsum : ∑ j ∈ Finset.univ.erase i, s j ≤ b) :
    s i * (a - b) ≤ (nu P).real (poolSet P s i ∩ Rset P s i c) := by
  rw [indep_split, nu_pool P s hs i]
  have hGR : Gset i c ⊆ Rset P s i c ∪ ⋃ j ∈ Finset.univ.erase i, poolSet P s j := by
    intro w hw
    by_cases h : ∀ j, j ≠ i → w ∉ poolSet P s j
    · exact Or.inl ⟨h, hw⟩
    · push Not at h
      obtain ⟨j, hj, hjw⟩ := h
      exact Or.inr (mem_biUnion (by simp [hj]) hjw)
  have h1 : (nu P).real (Gset i c) ≤ (nu P).real (Rset P s i c) +
      ∑ j ∈ Finset.univ.erase i, (nu P).real (poolSet P s j) := by
    calc (nu P).real (Gset i c) ≤ (nu P).real (Rset P s i c ∪ ⋃ j ∈ Finset.univ.erase i, poolSet P s j) :=
          measureReal_mono hGR
      _ ≤ (nu P).real (Rset P s i c) + (nu P).real (⋃ j ∈ Finset.univ.erase i, poolSet P s j) :=
          measureReal_union_le _ _
      _ ≤ _ := by
          gcongr
          exact measureReal_biUnion_finset_le _ _
  simp_rw [nu_pool P s hs] at h1
  rw [nu_Gset] at h1
  have : a - b ≤ (nu P).real (Rset P s i c) := by linarith
  exact mul_le_mul_of_nonneg_left this (hs i).1

end PersuasionByParts.Known.Dev.Single
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
noncomputable section

namespace PersuasionByParts.Known.Dev.Single
open PersuasionByParts.Known
open scoped Classical

variable {n : ℕ} (P : Prior n) (q t : ℝ)

theorem coordCap_bounds (i : Fin n) :
    0 ≤ coordinateCapacity P q t i ∧ coordinateCapacity P q t i ≤ 1 :=
  Iface.capacity_nonneg_le_one (P.marginal i) (P.finiteMean i) _

theorem sm_nonneg (hq : q ∈ Ioc (0:ℝ) 1) (i : Fin n) : 0 ≤ sparseMass P q t i := by
  unfold sparseMass
  split_ifs with h
  · have hb : 0 < totalCapacity P q t := lt_of_lt_of_le (by linarith [hq.1]) h
    exact div_nonneg (mul_nonneg (by linarith [hq.1]) (coordCap_bounds P q t i).1) hb.le
  · exact le_rfl

theorem cap_le_total (i : Fin n) : coordinateCapacity P q t i ≤ totalCapacity P q t :=
  Finset.single_le_sum (f := fun j => coordinateCapacity P q t j)
    (fun j _ => (coordCap_bounds P q t j).1) (Finset.mem_univ i)

theorem sm_le (hq : q ∈ Ioc (0:ℝ) 1) (i : Fin n) : sparseMass P q t i ≤ q / 6 := by
  unfold sparseMass
  split_ifs with h
  · have hb : 0 < totalCapacity P q t := lt_of_lt_of_le (by linarith [hq.1]) h
    rw [mul_div_assoc]
    have : coordinateCapacity P q t i / totalCapacity P q t ≤ 1 :=
      (div_le_one hb).2 (cap_le_total P q t i)
    nlinarith [hq.1]
  · linarith [hq.1]

theorem sm_mem (hq : q ∈ Ioc (0:ℝ) 1) (i : Fin n) : sparseMass P q t i ∈ Icc (0:ℝ) 1 :=
  ⟨sm_nonneg P q t hq i, by linarith [sm_le P q t hq i, hq.2]⟩

theorem sm_small (h : ¬ q / 6 ≤ totalCapacity P q t) (i : Fin n) : sparseMass P q t i = 0 := by
  unfold sparseMass; rw [if_neg h]

theorem sm_sum_big (hq : q ∈ Ioc (0:ℝ) 1) (h : q / 6 ≤ totalCapacity P q t) :
    ∑ i, sparseMass P q t i = q / 6 := by
  have hb : 0 < totalCapacity P q t := lt_of_lt_of_le (by linarith [hq.1]) h
  unfold sparseMass
  simp_rw [if_pos h]
  rw [← Finset.sum_div, ← Finset.mul_sum]
  have : ∑ i, coordinateCapacity P q t i = totalCapacity P q t := rfl
  rw [this]; field_simp

theorem sm_sum_le (hq : q ∈ Ioc (0:ℝ) 1) : ∑ i, sparseMass P q t i ≤ q / 6 := by
  by_cases h : q / 6 ≤ totalCapacity P q t
  · exact (sm_sum_big P q t hq h).le
  · simp [sm_small P q t h]; linarith [hq.1]

theorem sm_target (hq : q ∈ Ioc (0:ℝ) 1) (h : q / 6 ≤ totalCapacity P q t) (i : Fin n)
    (hpos : 0 < sparseMass P q t i) :
    target P q t i ≤ poolMean (P.marginal i) (sparseMass P q t i) := by
  have hb : 0 < totalCapacity P q t := lt_of_lt_of_le (by linarith [hq.1]) h
  have hsd : sparseMass P q t i = q / 6 * coordinateCapacity P q t i / totalCapacity P q t := by
    unfold sparseMass; rw [if_pos h]
  have hbi : 0 < coordinateCapacity P q t i := by
    by_contra hc
    have : coordinateCapacity P q t i = 0 := le_antisymm (not_lt.1 hc) (coordCap_bounds P q t i).1
    rw [this] at hsd; simp at hsd; linarith
  have hne : (capacitySet (P.marginal i) (target P q t i)).Nonempty := by
    by_contra hne
    have := Iface.capacity_eq_zero (P.marginal i) _ hne
    exact absurd this (ne_of_gt hbi)
  obtain ⟨hmem, -⟩ := Iface.capacity_spec (P.marginal i) (P.finiteMean i) _ hne
  have hmem' : coordinateCapacity P q t i ∈ capacitySet (P.marginal i) (target P q t i) := hmem
  have hsle : sparseMass P q t i ≤ coordinateCapacity P q t i := by
    have e : q / 6 * coordinateCapacity P q t i / totalCapacity P q t =
        (q / 6 / totalCapacity P q t) * coordinateCapacity P q t i := by ring
    rw [hsd, e]
    have h1 : q / 6 / totalCapacity P q t ≤ 1 := by
      rw [div_le_one hb]; exact h
    exact mul_le_of_le_one_left (coordCap_bounds P q t i).1 h1
  have := Iface.poolMean_antitoneOn (P.marginal i) (P.finiteMean i)
    (show sparseMass P q t i ∈ Ioc (0:ℝ) 1 from ⟨hpos, (sm_mem P q t hq i).2⟩)
    (show coordinateCapacity P q t i ∈ Ioc (0:ℝ) 1 from ⟨hmem'.1, hmem'.2.1⟩) hsle
  exact le_trans hmem'.2.2 this

theorem measurable_poolCount : Measurable (poolCount : (Fin n → Unit ⊕ ℝ) → ℝ) := by
  have : (poolCount : (Fin n → Unit ⊕ ℝ) → ℝ) =
      fun σ => ∑ i, Sum.elim (fun _ => (1:ℝ)) (fun _ => (0:ℝ)) (σ i) := by
    funext σ
    unfold poolCount
    refine Finset.sum_congr rfl fun i _ => ?_
    rcases hσ : σ i with u | r <;> simp [hσ]
  rw [this]
  exact Finset.measurable_sum _ fun i _ =>
    (Measurable.sumElim measurable_const measurable_const).comp (measurable_pi_apply i)

theorem claim1 (hq : q ∈ Ioc (0:ℝ) 1) :
    (∫ w, poolCount (fmap P (sparseMass P q t) w) ∂nu P) ≤ q / 6 := by
  set s := sparseMass P q t
  have hs := sm_mem P q t hq
  have e : ∀ w, poolCount (fmap P s w) = ∑ i, (poolSet P s i).indicator (fun _ => (1:ℝ)) w := by
    intro w; rw [count_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : w ∈ poolSet P s i <;> simp [h, indicator]
  simp_rw [e]
  rw [integral_finsetSum _ fun i _ => (integrable_const (1:ℝ)).indicator (measurableSet_poolSet P s i)]
  have : ∀ i, ∫ w, (poolSet P s i).indicator (fun _ => (1:ℝ)) w ∂nu P = s i := by
    intro i
    rw [integral_indicator_const _ (measurableSet_poolSet P s i), nu_pool P s hs i]; simp
  simp_rw [this]
  exact sm_sum_le P q t hq

end PersuasionByParts.Known.Dev.Single
end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
noncomputable section

namespace PersuasionByParts.Known.Dev.Single
open PersuasionByParts.Known
open scoped Classical

variable {n : ℕ} (P : Prior n) (q t : ℝ)

/-- The event `A` of the second claim, as a set of coupling points. -/
def evt (s : Fin n → ℝ) : Set (Fin n → ℝ × ℝ) :=
  {w | t ≤ ∑ i, PersuasionNetworks.posteriorMean (P.marginal i)
        (poolKernel (P.marginal i) (s i)) (fmap P s w i) ∧ poolCount (fmap P s w) ≤ 1}

theorem real_mono_ae {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {A B : Set α} (h : A ≤ᵐ[μ] B) : μ.real A ≤ μ.real B :=
  ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae h)

theorem nu_full : (nu P).real {w | t ≤ ∑ i, (w i).1} = revelationProbability P t := by
  have hm : MeasurableSet {x : Fin n → ℝ | t ≤ total x} :=
    measurableSet_le measurable_const (Dev.Cap.measurable_total)
  have hset : {w : Fin n → ℝ × ℝ | t ≤ ∑ i, (w i).1} =
      (fun (w : Fin n → ℝ × ℝ) j => (w j).1) ⁻¹' {x | t ≤ total x} := by
    ext w; simp [total]
  unfold revelationProbability
  rw [hset, measureReal_def, measureReal_def, ← law_x P,
    Measure.map_apply (f := fun (w : Fin n → ℝ × ℝ) j => (w j).1)
      (measurable_pi_iff.2 fun j => measurable_fst.comp (measurable_pi_apply j)) hm]

theorem claim2_small (hq : q ∈ Ioc (0:ℝ) 1) (ht : t ≤ poolMean (sumLaw P) q) (hn : 0 < n)
    (h : ¬ q / 6 ≤ totalCapacity P q t) :
    q ^ 2 / 36 ≤ (nu P).real (evt P t (sparseMass P q t)) := by
  set s := sparseMass P q t
  have hs := sm_mem P q t hq
  have hnull : ∀ᵐ w ∂(nu P), ∀ i, w ∉ poolSet P s i := by
    rw [ae_all_iff]
    intro i
    have h0 : (nu P).real (poolSet P s i) = 0 := by rw [nu_pool P s hs i]; exact sm_small P q t h i
    have := (measureReal_eq_zero_iff).1 h0
    exact measure_eq_zero_iff_ae_notMem.1 this
  have hpost := ae_post P s hs
  have hmono : {w : Fin n → ℝ × ℝ | t ≤ ∑ i, (w i).1} ≤ᵐ[nu P] evt P t s := by
    filter_upwards [hnull, hpost] with w hw hp hD
    refine ⟨?_, ?_⟩
    · rw [hp]
      have : ∑ i, (if w ∈ poolSet P s i then poolMean (P.marginal i) (s i) else (w i).1) =
          ∑ i, (w i).1 :=
        Finset.sum_congr rfl fun i _ => by simp [hw i]
      rw [this]; exact hD
    · rw [count_eq]
      have : ∑ i, (if w ∈ poolSet P s i then (1:ℝ) else 0) = 0 :=
        Finset.sum_eq_zero fun i _ => by simp [hw i]
      rw [this]; norm_num
  have h1 := real_mono_ae (nu P) hmono
  rw [nu_full] at h1
  have := ((chk_capacity_lemma P hn q t hq ht).2 (not_le.1 h))
  linarith

theorem tail_ge (hq : q ∈ Ioc (0:ℝ) 1) (i : Fin n) :
    q / 3 ≤ (priorLaw P).real {x | t - target P q t i ≤ others i x} := by
  have hu : q / 3 ∈ Ioo (0:ℝ) 1 := ⟨by linarith [hq.1], by linarith [hq.2]⟩
  have h := Dev.Pool.le_real_Ici (othersLaw P i) hu
  have e : {x : Fin n → ℝ | t - target P q t i ≤ others i x} =
      others i ⁻¹' Ici (quantile (othersLaw P i) (1 - q / 3)) := by
    ext x; simp [target]
  rw [e]
  have : (priorLaw P).real (others i ⁻¹' Ici (quantile (othersLaw P i) (1 - q / 3))) =
      (othersLaw P i).real (Ici (quantile (othersLaw P i) (1 - q / 3))) := by
    unfold othersLaw
    rw [Measure.real, Measure.real, Measure.map_apply (Dev.Cap.measurable_others i) measurableSet_Ici]
  rw [this]; exact h

theorem claim2_big (hq : q ∈ Ioc (0:ℝ) 1) (h : q / 6 ≤ totalCapacity P q t) :
    q ^ 2 / 36 ≤ (nu P).real (evt P t (sparseMass P q t)) := by
  set s := sparseMass P q t with hsdef
  have hs := sm_mem P q t hq
  have hsum : ∑ i, s i = q / 6 := sm_sum_big P q t hq h
  set Di : Fin n → Set (Fin n → ℝ × ℝ) := fun i =>
    if 0 < s i then poolSet P s i ∩ Rset P s i (t - target P q t i) else ∅ with hDi
  have hDm : ∀ i, MeasurableSet (Di i) := by
    intro i; simp only [hDi]; split_ifs
    · exact (measurableSet_poolSet P s i).inter (measurableSet_Rset P s i _)
    · exact MeasurableSet.empty
  have hmemD : ∀ i w, w ∈ Di i → 0 < s i ∧ w ∈ poolSet P s i ∩ Rset P s i (t - target P q t i) := by
    intro i w hw
    simp only [hDi] at hw
    split_ifs at hw with hp
    · exact ⟨hp, hw⟩
    · exact absurd hw (notMem_empty w)
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin n))) Di := by
    intro i _ j _ hij
    refine Set.disjoint_left.2 fun w hwi hwj => ?_
    have h1 := hmemD i w hwi
    have h2 := hmemD j w hwj
    exact (h2.2.2.1 i hij) h1.2.1
  have hmono : (⋃ i ∈ (Finset.univ : Finset (Fin n)), Di i) ≤ᵐ[nu P] evt P t s := by
    filter_upwards [ae_post P s hs] with w hp hw
    obtain ⟨i, -, hwi⟩ := mem_iUnion₂.1 hw
    obtain ⟨hpos, hpool, hR⟩ := hmemD i w hwi
    have hh := sm_target P q t hq h i hpos
    have hsplit : ∀ g : Fin n → ℝ, ∑ j, g j = g i + ∑ j ∈ Finset.univ.erase i, g j := fun g =>
      (Finset.add_sum_erase _ g (Finset.mem_univ i)).symm
    refine ⟨?_, ?_⟩
    · rw [hp, hsplit]
      have e2 : ∑ j ∈ Finset.univ.erase i,
          (if w ∈ poolSet P s j then poolMean (P.marginal j) (s j) else (w j).1) =
          ∑ j ∈ Finset.univ.erase i, (w j).1 :=
        Finset.sum_congr rfl fun j hj => by
          have hji : j ≠ i := (Finset.mem_erase.1 hj).1
          simp [hR.1 j hji]
      rw [e2, if_pos hpool]
      have := hR.2
      linarith
    · rw [count_eq, hsplit]
      have e2 : ∑ j ∈ Finset.univ.erase i, (if w ∈ poolSet P s j then (1:ℝ) else 0) = 0 :=
        Finset.sum_eq_zero fun j hj => by
          have hji : j ≠ i := (Finset.mem_erase.1 hj).1
          simp [hR.1 j hji]
      rw [e2, if_pos hpool]; norm_num
  have h1 := real_mono_ae (nu P) hmono
  rw [measureReal_biUnion_finset hdisj (fun i _ => hDm i)] at h1
  have h2 : ∀ i, s i * (q / 6) ≤ (nu P).real (Di i) := by
    intro i
    by_cases hp : 0 < s i
    · have e : Di i = poolSet P s i ∩ Rset P s i (t - target P q t i) := by simp only [hDi]; rw [if_pos hp]
      rw [e]
      have hsum' : ∑ j ∈ Finset.univ.erase i, s j ≤ q / 6 := by
        calc ∑ j ∈ Finset.univ.erase i, s j ≤ ∑ j, s j :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun j _ _ => (hs j).1)
          _ = q / 6 := hsum
      have := lb P s hs i (t - target P q t i) (q / 3) (q / 6) (tail_ge P q t hq i) hsum'
      calc s i * (q / 6) = s i * (q / 3 - q / 6) := by ring
        _ ≤ _ := this
    · have : s i = 0 := le_antisymm (not_lt.1 hp) (hs i).1
      rw [this, zero_mul]; exact measureReal_nonneg
  calc q ^ 2 / 36 = (∑ i, s i) * (q / 6) := by rw [hsum]; ring
    _ = ∑ i, s i * (q / 6) := Finset.sum_mul _ _ _
    _ ≤ ∑ i, (nu P).real (Di i) := Finset.sum_le_sum fun i _ => h2 i
    _ ≤ _ := h1

end PersuasionByParts.Known.Dev.Single

namespace PersuasionByParts.Known

/-- Lemma 2.4, printed p. 8 / PDF p. 9: both claims refer to the same explicitly
constructed experiment, in both capacity regimes. -/
theorem chk_single_cutoff_experiment {n : ℕ} (P : Prior n) (hn : 0 < n)
    (q t : ℝ) (hq : q ∈ Ioc 0 1) (ht : t ≤ poolMean (sumLaw P) q) :
    let E := sparseExperiment P q t
    (∫ s, poolCount s ∂productSignalLaw P E) ≤ q / 6 ∧
    (productSignalLaw P E).real
      {s | t ≤ productPosterior P E s ∧ poolCount s ≤ 1} ≥ q ^ 2 / 36 := by
  intro E
  have hL : productSignalLaw P E = (Dev.Single.nu P).map (Dev.Single.fmap P (sparseMass P q t)) :=
    Dev.Single.law_eq P (sparseMass P q t)
  have hf := Dev.Single.measurable_fmap P (sparseMass P q t)
  refine ⟨?_, ?_⟩
  · rw [hL]
    have key : ∫ σ, poolCount σ ∂((Dev.Single.nu P).map (Dev.Single.fmap P (sparseMass P q t))) =
        ∫ w, poolCount (Dev.Single.fmap P (sparseMass P q t) w) ∂Dev.Single.nu P :=
      integral_map hf.aemeasurable Dev.Single.measurable_poolCount.aestronglyMeasurable
    exact key.trans_le (Dev.Single.claim1 P q t hq)
  · rw [hL]
    have h1 : (Dev.Single.nu P).real (Dev.Single.evt P t (sparseMass P q t)) ≤
        ((Dev.Single.nu P).map (Dev.Single.fmap P (sparseMass P q t))).real
          {s | t ≤ productPosterior P E s ∧ poolCount s ≤ 1} := by
      refine ENNReal.toReal_mono (measure_ne_top _ _) ?_
      exact Measure.le_map_apply hf.aemeasurable _
    have h2 : q ^ 2 / 36 ≤ (Dev.Single.nu P).real (Dev.Single.evt P t (sparseMass P q t)) := by
      by_cases h : q / 6 ≤ totalCapacity P q t
      · exact Dev.Single.claim2_big P q t hq h
      · exact Dev.Single.claim2_small P q t hq ht hn h
    exact le_trans h2 h1

end PersuasionByParts.Known

end
end

theorem solution : type_of% @PersuasionByParts.Known.chk_single_cutoff_experiment := @PersuasionByParts.Known.chk_single_cutoff_experiment
