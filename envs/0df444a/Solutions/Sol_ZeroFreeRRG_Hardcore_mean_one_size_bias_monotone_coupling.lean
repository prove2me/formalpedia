-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.mean_one_size_bias_monotone_coupling
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:24:20.364972+00:00
-- url     : https://prove2.me/submissions/ad2a32df-ebc9-4b5e-992c-5cc13ba04595

import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal

private theorem coupling_marginals {X : Type} [MeasurableSpace X] (common low high : Measure X)
    [IsFiniteMeasure common] [IsFiniteMeasure low] [IsFiniteMeasure high]
    (hmass : low univ = high univ) (h0 : low univ ≠ 0) :
    let π : Measure (X × X) := Measure.map (fun x => (x,x)) common +
      (low univ)⁻¹ • (low.prod high)
    Measure.map Prod.fst π = common+low ∧ Measure.map Prod.snd π = common+high := by
  classical
  have hf : Measurable (fun x : X => (x,x)) := measurable_id.prodMk measurable_id
  have hfin : low univ ≠ ∞ := measure_ne_top _ _
  have hc : (low univ)⁻¹ * low univ = 1 := ENNReal.inv_mul_cancel h0 hfin
  constructor
  · rw [Measure.map_add _ _ measurable_fst, Measure.map_smul, Measure.map_map measurable_fst hf,
      Measure.map_fst_prod]
    simp only [Function.comp_def, Measure.map_id, ← hmass, smul_smul, hc, one_smul]
    change Measure.map id common + low = common + low
    rw [Measure.map_id]
  · rw [Measure.map_add _ _ measurable_snd, Measure.map_smul, Measure.map_map measurable_snd hf,
      Measure.map_snd_prod]
    simp only [Function.comp_def, Measure.map_id, smul_smul, hc, one_smul]
    change Measure.map id common + high = common + high
    rw [Measure.map_id]

private theorem ordered_coupling (common low high : Measure ℝ)
    [IsFiniteMeasure common] [IsFiniteMeasure low] [IsFiniteMeasure high]
    (hmass : low univ = high univ) (h0 : low univ ≠ 0) (t : ℝ)
    (hlow : ∀ᵐ x ∂low, x ≤ t) (hhigh : ∀ᵐ y ∂high, t ≤ y) :
    let π : Measure (ℝ × ℝ) := Measure.map (fun x => (x,x)) common +
      (low univ)⁻¹ • (low.prod high)
    Measure.map Prod.fst π = common+low ∧ Measure.map Prod.snd π = common+high ∧
      (∀ᵐ p ∂π, p.1 ≤ p.2) := by
  have hm := coupling_marginals common low high hmass h0
  refine ⟨hm.1,hm.2,?_⟩
  have hdiag : ∀ᵐ p ∂(Measure.map (fun x : ℝ => (x,x)) common), p.1 ≤ p.2 := by
    apply (ae_map_iff (measurable_id.prodMk measurable_id).aemeasurable
      (measurableSet_le measurable_fst measurable_snd)).2
    exact Filter.Eventually.of_forall (fun _ => le_rfl)
  have hprod : ∀ᵐ p ∂(low.prod high), p.1 ≤ p.2 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le measurable_fst measurable_snd)).2
    filter_upwards [hlow] with x hx
    filter_upwards [hhigh] with y hy
    exact hx.trans hy
  have hscale := Measure.ae_smul_measure hprod ((low univ)⁻¹)
  apply ae_iff.mpr
  rw [Measure.add_apply,ae_iff.mp hdiag,ae_iff.mp hscale,add_zero]


private noncomputable def lo (x : ℝ) := max (1-x) 0
private noncomputable def hi (x : ℝ) := max (x-1) 0
private noncomputable def mid (x : ℝ) := min x 1

private theorem lo_hi_diff (x : ℝ) : lo x - hi x = 1-x := by
  dsimp [lo,hi]
  rcases le_total x 1 with h | h
  · rw [max_eq_left (by linarith),max_eq_right (by linarith)]
    ring
  · rw [max_eq_right (by linarith),max_eq_left (by linarith)]
    ring
private theorem mid_lo (x : ℝ) : mid x + lo x = 1 := by
  dsimp [mid,lo]
  rcases le_total x 1 with h | h
  · rw [min_eq_left h,max_eq_left (by linarith)]
    ring
  · rw [min_eq_right h,max_eq_right (by linarith)]
    ring
private theorem mid_hi (x : ℝ) : mid x + hi x = x := by
  dsimp [mid,hi]
  rcases le_total x 1 with h | h
  · rw [min_eq_left h,max_eq_right (by linarith)]
    ring
  · rw [min_eq_right h,max_eq_left (by linarith)]
    ring

theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hpos : ∀ᵐ x ∂μ, 0 ≤ x) (hint : Integrable (fun x => x) μ)
    (hmean : (∫ x, x ∂μ) = 1) :
    ∃ π : Measure (ℝ × ℝ), IsProbabilityMeasure π ∧
      Measure.map Prod.fst π = μ ∧
      Measure.map Prod.snd π = μ.withDensity (fun x => ENNReal.ofReal x) ∧
      (∀ᵐ p ∂π, p.1 ≤ p.2) := by
  let low := μ.withDensity (fun x => ENNReal.ofReal (lo x))
  let high := μ.withDensity (fun x => ENNReal.ofReal (hi x))
  let common := μ.withDensity (fun x => ENNReal.ofReal (mid x))
  have hmlo : Measurable lo := by unfold lo; fun_prop
  have hmhi : Measurable hi := by unfold hi; fun_prop
  have hmmid : Measurable mid := by unfold mid; fun_prop
  have hloint : Integrable lo μ := by
    change Integrable ((fun x : ℝ => 1-x) ⊔ (fun _ => 0)) μ
    exact ((integrable_const 1).sub hint).sup (integrable_const 0)
  have hhiint : Integrable hi μ := by
    change Integrable ((fun x : ℝ => x-1) ⊔ (fun _ => 0)) μ
    exact (hint.sub (integrable_const 1)).sup (integrable_const 0)
  have hmidint : Integrable mid μ := by
    change Integrable ((fun x : ℝ => x) ⊓ (fun _ => 1)) μ
    exact hint.inf (integrable_const 1)
  letI : IsFiniteMeasure low := isFiniteMeasure_withDensity_ofReal hloint.hasFiniteIntegral
  letI : IsFiniteMeasure high := isFiniteMeasure_withDensity_ofReal hhiint.hasFiniteIntegral
  letI : IsFiniteMeasure common := isFiniteMeasure_withDensity_ofReal hmidint.hasFiniteIntegral
  have hlo0 : ∀ x, 0 ≤ lo x := fun x => le_max_right _ _
  have hhi0 : ∀ x, 0 ≤ hi x := fun x => le_max_right _ _
  have hmid0 : ∀ᵐ x ∂μ, 0 ≤ mid x := by
    filter_upwards [hpos] with x hx
    exact le_min hx (by norm_num)
  have hdiff : (∫ x, lo x ∂μ) = ∫ x, hi x ∂μ := by
    have h := integral_sub hloint hhiint
    have hh : (fun x => lo x - hi x) = fun x => 1-x := funext lo_hi_diff
    rw [hh, integral_sub (integrable_const 1) hint] at h
    simp only [integral_const, probReal_univ, one_smul,hmean,sub_self] at h
    linarith
  have hmass : low univ = high univ := by
    dsimp [low,high]
    rw [withDensity_apply _ MeasurableSet.univ, withDensity_apply _ MeasurableSet.univ]
    simp only [Measure.restrict_univ]
    rw [← ofReal_integral_eq_lintegral_ofReal hloint (Filter.Eventually.of_forall hlo0),
        ← ofReal_integral_eq_lintegral_ofReal hhiint (Filter.Eventually.of_forall hhi0), hdiff]
  have hcommonlow : common + low = μ := by
    dsimp [common,low]
    rw [← withDensity_add_left hmmid.ennreal_ofReal]
    calc
      _ = μ.withDensity 1 := by
        apply withDensity_congr_ae
        filter_upwards [hmid0] with x hx
        change ENNReal.ofReal (mid x) + ENNReal.ofReal (lo x) = 1
        rw [← ENNReal.ofReal_add hx (hlo0 x),mid_lo]
        simp
      _ = μ := withDensity_one
  have hcommonhigh : common + high = μ.withDensity (fun x => ENNReal.ofReal x) := by
    dsimp [common,high]
    rw [← withDensity_add_left hmmid.ennreal_ofReal]
    apply withDensity_congr_ae
    filter_upwards [hmid0] with x hx
    change ENNReal.ofReal (mid x) + ENNReal.ofReal (hi x) = ENNReal.ofReal x
    rw [← ENNReal.ofReal_add hx (hhi0 x),mid_hi]
  have hlow : ∀ᵐ x ∂low, x ≤ 1 := by
    apply ae_iff.mpr
    dsimp [low]
    change (μ.withDensity (fun x => ENNReal.ofReal (lo x))) (Iic (1:ℝ))ᶜ = 0
    rw [withDensity_apply _ measurableSet_Iic.compl]
    apply (lintegral_eq_zero_iff' hmlo.ennreal_ofReal.aemeasurable).2
    filter_upwards [ae_restrict_mem measurableSet_Iic.compl] with x hx
    have hx' : 1 ≤ x := by
      change ¬x ≤ 1 at hx
      exact le_of_lt (lt_of_not_ge hx)
    simp [lo,max_eq_right (show 1-x ≤ 0 by linarith)]
  have hhigh : ∀ᵐ x ∂high, 1 ≤ x := by
    apply ae_iff.mpr
    dsimp [high]
    change (μ.withDensity (fun x => ENNReal.ofReal (hi x))) (Ici (1:ℝ))ᶜ = 0
    rw [withDensity_apply _ measurableSet_Ici.compl]
    apply (lintegral_eq_zero_iff' hmhi.ennreal_ofReal.aemeasurable).2
    filter_upwards [ae_restrict_mem measurableSet_Ici.compl] with x hx
    have hx' : x ≤ 1 := by
      change ¬1 ≤ x at hx
      exact le_of_lt (lt_of_not_ge hx)
    simp [hi,max_eq_right (show x-1 ≤ 0 by linarith)]
  by_cases hz : low univ = 0
  · have hlo : low = 0 := Measure.measure_univ_eq_zero.mp hz
    have hhi : high = 0 := Measure.measure_univ_eq_zero.mp (hmass.symm.trans hz)
    have hμ : common = μ := by simpa [hlo] using hcommonlow
    have hν : common = μ.withDensity (fun x => ENNReal.ofReal x) := by simpa [hhi] using hcommonhigh
    let π := Measure.map (fun x : ℝ => (x,x)) common
    have hf : Measurable (fun x : ℝ => (x,x)) := measurable_id.prodMk measurable_id
    have hfst : Measure.map Prod.fst π = μ := by
      dsimp [π]; rw [Measure.map_map measurable_fst hf]; change Measure.map id common = μ; rw [Measure.map_id,hμ]
    have hsnd : Measure.map Prod.snd π = μ.withDensity (fun x => ENNReal.ofReal x) := by
      dsimp [π]; rw [Measure.map_map measurable_snd hf]; change Measure.map id common = _; rw [Measure.map_id,hν]
    have hprob : IsProbabilityMeasure π := by
      apply isProbabilityMeasure_iff.mpr
      have hh := congrArg (fun m : Measure ℝ => m univ) hfst
      rw [Measure.map_apply measurable_fst MeasurableSet.univ] at hh
      simpa using hh
    refine ⟨π,hprob,hfst,hsnd,?_⟩
    apply (ae_map_iff hf.aemeasurable (measurableSet_le measurable_fst measurable_snd)).2
    exact Filter.Eventually.of_forall (fun _ => le_rfl)
  · let π := Measure.map (fun x : ℝ => (x,x)) common + (low univ)⁻¹ • (low.prod high)
    have hh := ordered_coupling common low high hmass hz 1 hlow hhigh
    have hfst : Measure.map Prod.fst π = μ := hh.1.trans hcommonlow
    have hsnd : Measure.map Prod.snd π = μ.withDensity (fun x => ENNReal.ofReal x) := hh.2.1.trans hcommonhigh
    have hprob : IsProbabilityMeasure π := by
      apply isProbabilityMeasure_iff.mpr
      have hh := congrArg (fun m : Measure ℝ => m univ) hfst
      rw [Measure.map_apply measurable_fst MeasurableSet.univ] at hh
      simpa using hh
    exact ⟨π,hprob,hfst,hsnd,hh.2.2⟩
