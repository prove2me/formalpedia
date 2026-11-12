-- Prove2me | solution 1 for PersuasionByParts.Known.pooling_semantics
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T16:55:05.996678+00:00
-- url     : https://prove2.me/submissions/c0921c75-be76-4b9d-9f3f-b2585b4162be

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

theorem G_eq (s : ℝ) : poolMean μ s = (∫ u in (1 - s)..1, quantile μ u) / s := rfl


theorem poolMean_one' (hμ : Integrable id μ) : poolMean μ 1 = ∫ x, x ∂μ := by
  rw [G_eq]
  simp only [sub_self, div_one]
  rw [intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo]
  exact (integral_quantile μ id aestronglyMeasurable_id).symm


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


end PersuasionByParts.Known.Dev.Pool

/-! ### Interface statements -/

namespace PersuasionByParts.Known.Iface
open PersuasionByParts.Known.Dev.Pool

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

/-- Section 1.1, unnumbered top-pool definition and mean identity, printed p. 3.
The mean at a zero-mass pool is never asserted to be a conditional mean. -/
theorem chk_pooling_semantics (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) (s : ℝ) (hs : s ∈ Icc 0 1) :
    (∀ z : ℝ, topSelector μ s z ∈ Icc 0 1) ∧
    (∫ z, topSelector μ s z ∂μ) = s ∧
    (∫ z, topSelector μ s z * z ∂μ) = s * poolMean μ s ∧
    (poolKernel μ s ∘ₘ μ).real {Sum.inl ()} = s ∧
    (0 < s → PersuasionNetworks.posteriorMean μ (poolKernel μ s) (Sum.inl ()) =
      poolMean μ s) := by
  haveI := Dev.PS.msc
  obtain ⟨hmem, hint, hmom⟩ := Dev.Pool.top_spec μ hμ hs
  have hker : ∀ x, (poolKernel μ s x).real {Sum.inl ()} = topSelector μ s x := fun x => by
    rw [measureReal_def, Dev.PS.poolKernel_inl μ s x (hmem x),
      ENNReal.toReal_ofReal (hmem x).1]
  have h4 : (poolKernel μ s ∘ₘ μ).real {Sum.inl ()} = s := by
    rw [Dev.Post.real_comp_apply (poolKernel μ s) μ (measurableSet_singleton _)]
    simp_rw [hker]; exact hint
  refine ⟨hmem, hint, hmom, h4, fun hs0 => ?_⟩
  have := Dev.Post.posterior_integral_atom (poolKernel μ s) μ (fun x => x) measurable_id hμ
    (Sum.inl ())
  rw [h4] at this
  simp_rw [hker] at this
  have e : ∀ x : ℝ, x * topSelector μ s x = topSelector μ s x * x := fun x => mul_comm _ _
  simp_rw [e, hmom] at this
  unfold PersuasionNetworks.posteriorMean
  exact mul_left_cancel₀ hs0.ne' this

end PersuasionByParts.Known
end
end

theorem solution : type_of% @PersuasionByParts.Known.chk_pooling_semantics := @PersuasionByParts.Known.chk_pooling_semantics
