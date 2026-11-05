-- Prove2me | solution 1 for WassVarReg.PInf.theorem_1_I
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T19:49:50.738456+00:00
-- url     : https://prove2.me/submissions/3addee75-0104-4567-bc6d-883befbecdf2

import Mathlib
import Definitions.Def_WassVarReg_PInf_Setting

open MeasureTheory Filter
open scoped ENNReal NNReal

namespace WVR2Aux

lemma toENNReal_coe_real (x : ℝ) : ((x : EReal)).toENNReal = ENNReal.ofReal x := by
  rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top x)]; simp

lemma nominalRisk_eq_integral {E : Type*} [MeasurableSpace E] (μ : Measure E) (f : E → ℝ)
    (hf : Integrable f μ) :
    WassersteinDRO.Duality.nominalRisk μ f = ((∫ x, f x ∂μ : ℝ) : EReal) := by
  unfold WassersteinDRO.Duality.nominalRisk WassersteinDRO.Duality.erealExpectation
  have h1 : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ⊤ :=
    ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hf.2).ne
  have h2 : ∫⁻ x, ENNReal.ofReal (-f x) ∂μ ≠ ⊤ :=
    ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hf.neg.2).ne
  simp only [toENNReal_coe_real, ← EReal.coe_neg]
  rw [if_neg h1, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf,
    EReal.coe_sub, EReal.coe_ennreal_toReal h1, EReal.coe_ennreal_toReal h2]

/-- Upper bound for nominalRisk. -/
lemma nominalRisk_le {E : Type*} [MeasurableSpace E] (μ : Measure E) (f : E → ℝ)
    (hfm : Measurable f) (C : ℝ)
    (hpos : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≠ ⊤)
    (hC : Integrable f μ → ∫ x, f x ∂μ ≤ C) :
    WassersteinDRO.Duality.nominalRisk μ f ≤ (C : EReal) := by
  by_cases hi : Integrable f μ
  · rw [nominalRisk_eq_integral μ f hi]; exact_mod_cast hC hi
  · unfold WassersteinDRO.Duality.nominalRisk WassersteinDRO.Duality.erealExpectation
    simp only [toENNReal_coe_real, ← EReal.coe_neg]
    rw [if_neg hpos]
    have hneg : ∫⁻ x, ENNReal.ofReal (-f x) ∂μ = ⊤ := by
      by_contra hne
      apply hi
      refine ⟨hfm.aestronglyMeasurable, ?_⟩
      have : ∫⁻ x, ‖f x‖ₑ ∂μ = ∫⁻ x, ENNReal.ofReal (f x) ∂μ + ∫⁻ x, ENNReal.ofReal (-f x) ∂μ := by
        rw [← lintegral_add_left hfm.ennreal_ofReal]
        congr 1; ext x
        rcases le_total 0 (f x) with h | h
        · rw [Real.enorm_eq_ofReal h, ENNReal.ofReal_of_nonpos (by linarith : -f x ≤ 0), add_zero]
        · rw [Real.enorm_eq_ofReal_abs, abs_of_nonpos h, ENNReal.ofReal_of_nonpos h, zero_add]
      show ∫⁻ x, ‖f x‖ₑ ∂μ < ⊤
      rw [this]; exact ENNReal.add_lt_top.2 ⟨lt_top_iff_ne_top.2 hpos, lt_top_iff_ne_top.2 hne⟩
    rw [hneg]
    simp

lemma empiricalPM_eq {Z : Type*} [MeasurableSpace Z] {n : ℕ} (hn : 0 < n) (ω : Fin n → Z) :
    (MinimaxWass.DataDep.empiricalPM hn ω : Measure Z) =
      ((n : ℝ≥0∞)⁻¹) • ∑ i : Fin n, Measure.dirac (ω i) := by
  let _ : Nonempty Z := ⟨ω ⟨0, hn⟩⟩
  let fm : FiniteMeasure Z := ⟨∑ i : Fin n, Measure.dirac (ω i), inferInstance⟩
  have hfm : (fm : Measure Z) = ∑ i : Fin n, Measure.dirac (ω i) := rfl
  have hmass : fm.mass = n := by
    rw [FiniteMeasure.mass]
    apply ENNReal.coe_injective
    rw [FiniteMeasure.ennreal_coeFn_eq_coeFn_toMeasure, hfm]
    simp
  have hne : fm ≠ 0 := by
    intro h
    have : fm.mass = 0 := by rw [h]; simp
    rw [hmass] at this; exact (Nat.cast_ne_zero.2 hn.ne') this
  show (FiniteMeasure.normalize fm : Measure Z) = _
  rw [FiniteMeasure.toMeasure_normalize_eq_of_nonzero fm hne, hmass, hfm]
  ext s hs
  simp only [Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply, smul_eq_mul]
  rw [ENNReal.smul_def, smul_eq_mul, ENNReal.coe_inv (by exact_mod_cast hn.ne'),
    ENNReal.coe_natCast]


lemma integrable_empiricalPM {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {n : ℕ} (hn : 0 < n) (ω : Fin n → Z) (g : Z → ℝ) :
    Integrable g (MinimaxWass.DataDep.empiricalPM hn ω : Measure Z) := by
  rw [empiricalPM_eq]
  refine Integrable.smul_measure ?_ (by simp [hn.ne'])
  exact integrable_finset_sum_measure.2 (fun i _ => integrable_dirac enorm_lt_top)

lemma integral_empiricalPM {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {n : ℕ} (hn : 0 < n) (ω : Fin n → Z) (g : Z → ℝ) :
    ∫ x, g x ∂(MinimaxWass.DataDep.empiricalPM hn ω : Measure Z) =
      (1 / (n : ℝ)) * ∑ i : Fin n, g (ω i) := by
  rw [empiricalPM_eq, integral_smul_measure,
    integral_finset_sum_measure (fun i _ => integrable_dirac enorm_lt_top)]
  simp [integral_dirac]

lemma ae_mem_range_empiricalPM {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {n : ℕ} (hn : 0 < n) (ω : Fin n → Z) :
    ∀ᵐ x ∂(MinimaxWass.DataDep.empiricalPM hn ω : Measure Z), x ∈ Set.range ω := by
  rw [empiricalPM_eq, ae_iff]
  have hms : MeasurableSet (Set.range ω)ᶜ := (Set.finite_range ω).measurableSet.compl
  have : {a | a ∉ Set.range ω} = (Set.range ω)ᶜ := rfl
  rw [this, Measure.smul_apply, Measure.finset_sum_apply]
  simp [Measure.dirac_apply' _ hms]

lemma map_empiricalPM {Z Y : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    {n : ℕ} (hn : 0 < n) (ω : Fin n → Z) (g : Z → Y) (hg : Measurable g) :
    (MinimaxWass.DataDep.empiricalPM hn ω : Measure Z).map g =
      (MinimaxWass.DataDep.empiricalPM hn (g ∘ ω) : Measure Y) := by
  rw [empiricalPM_eq, empiricalPM_eq]
  ext s hs
  rw [Measure.map_apply hg hs, Measure.smul_apply, Measure.smul_apply,
    Measure.finset_sum_apply, Measure.finset_sum_apply]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Measure.dirac_apply' _ (hg hs), Measure.dirac_apply' _ hs]
  simp only [Set.indicator, Function.comp_apply, Pi.one_apply]
  by_cases h : g (ω i) ∈ s
  · rw [if_pos h, if_pos (show ω i ∈ g ⁻¹' s from h)]
  · rw [if_neg h, if_neg (show ω i ∉ g ⁻¹' s from h)]


lemma measurable_indicator_finite {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    (S : Set Z) (hS : S.Finite) (b : Z → ℝ) : Measurable (S.indicator b) := by
  intro t ht
  rw [Set.indicator_preimage]
  show MeasurableSet ((b ⁻¹' t ∩ S) ∪ ((0 : Z → ℝ) ⁻¹' t \ S))
  exact ((hS.subset Set.inter_subset_right).measurableSet).union
    ((measurable_const (a := (0 : ℝ)) ht).diff hS.measurableSet)


open WassVarReg.PInf in
lemma le_Gf {Z : Type*} [MetricSpace Z] (f : Z → ℝ) (r : ℝ) (z z' : Z)
    (h : dist z' z ≤ r) : ((f z' - f z : ℝ) : EReal) ≤ Gf f r z := by
  unfold Gf
  exact le_iSup₂ (f := fun (z' : Z) (_ : dist z' z ≤ r) => ((f z' - f z : ℝ) : EReal)) z' h

open WassVarReg.PInf in
lemma Gf_nonneg {Z : Type*} [MetricSpace Z] (f : Z → ℝ) (r : ℝ) (hr : 0 ≤ r) (z : Z) :
    (0 : EReal) ≤ Gf f r z := by
  have := le_Gf f r z z (by simpa using hr)
  simpa using this

open WassVarReg.PInf in
lemma Gf_coe {Z : Type*} [MetricSpace Z] (f : Z → ℝ) (r : ℝ) (hr : 0 ≤ r) (z : Z)
    (hG : Gf f r z ≠ ⊤) : (((Gf f r z).toReal : ℝ) : EReal) = Gf f r z :=
  EReal.coe_toReal hG (ne_bot_of_le_ne_bot (by simp) (Gf_nonneg f r hr z))

open WassVarReg.PInf in
lemma upper_bound {Z : Type*} [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    {n : ℕ} (hn : 0 < n) (ω : Fin n → Z) (f : Z → ℝ) (hf : Measurable f)
    (P : ProbabilityMeasure Z) (r : ℝ) (hr : 0 ≤ r) (γ : Measure (Z × Z))
    (hγ : γ ∈ WassersteinLinOpt.Ball.couplings (P : Measure Z)
      (MinimaxWass.DataDep.empiricalPM hn ω : Measure Z))
    (hae : ∀ᵐ x ∂γ, dist x.1 x.2 ≤ r) (hG : ∀ i, Gf f r (ω i) ≠ ⊤) :
    WassersteinDRO.Duality.nominalRisk (P : Measure Z) f ≤
      (((1 / (n : ℝ)) * ∑ i : Fin n, (f (ω i) + (Gf f r (ω i)).toReal) : ℝ) : EReal) := by
  obtain ⟨h1, h2⟩ := hγ
  have : IsProbabilityMeasure γ := by
    constructor
    have := congrArg (fun μ : Measure Z => μ Set.univ) h1
    rw [Measure.map_apply measurable_fst MeasurableSet.univ] at this
    simpa using this
  set S := Set.range ω with hS
  set b : Z → ℝ := fun z => f z + (Gf f r z).toReal with hb
  set c : Z → ℝ := S.indicator b with hc
  have hcm : Measurable c := measurable_indicator_finite S (Set.finite_range ω) b
  have hsupp : ∀ᵐ x ∂γ, x.2 ∈ S := by
    have := ae_mem_range_empiricalPM hn ω
    rw [← h2] at this
    exact ae_of_ae_map measurable_snd.aemeasurable this
  have hle : ∀ᵐ x ∂γ, f x.1 ≤ c x.2 := by
    filter_upwards [hae, hsupp] with x hx hxS
    obtain ⟨i, hi⟩ := hxS
    have hcx : c x.2 = b x.2 := Set.indicator_of_mem (show x.2 ∈ S from ⟨i, hi⟩) b
    rw [hcx, hb]
    have key := le_Gf f r x.2 x.1 hx
    rw [← hi] at key ⊢
    rw [← Gf_coe f r hr (ω i) (hG i)] at key
    have : f x.1 - f (ω i) ≤ (Gf f r (ω i)).toReal := by exact_mod_cast key
    simp only; linarith
  have hcint : Integrable (fun x : Z × Z => c x.2) γ := by
    have : Integrable c (γ.map Prod.snd) := by rw [h2]; exact integrable_empiricalPM hn ω c
    exact (integrable_map_measure hcm.aestronglyMeasurable measurable_snd.aemeasurable).1 this
  have hcsum : ∫ x, c x.2 ∂γ = (1 / (n : ℝ)) * ∑ i : Fin n, (f (ω i) + (Gf f r (ω i)).toReal) := by
    have := integral_map (μ := γ) measurable_snd.aemeasurable hcm.aestronglyMeasurable
    rw [← this, h2, integral_empiricalPM]
    congr 1
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hc, Set.indicator_of_mem (show ω i ∈ S from ⟨i, rfl⟩) b]
  apply nominalRisk_le _ f hf
  · rw [← h1, lintegral_map hf.ennreal_ofReal measurable_fst]
    refine ne_top_of_le_ne_top ?_ (lintegral_mono_ae (hle.mono fun x hx => ENNReal.ofReal_le_ofReal hx))
    exact ((lintegral_ofReal_le_lintegral_enorm _).trans_lt hcint.2).ne
  · intro hfi
    rw [← h1] at hfi ⊢
    rw [integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable, ← hcsum]
    have hfi' : Integrable (fun x : Z × Z => f x.1) γ :=
      (integrable_map_measure hf.aestronglyMeasurable measurable_fst.aemeasurable).1 hfi
    exact integral_mono_ae hfi' hcint hle


lemma nominalRisk_empiricalPM {Z : Type*} [MeasurableSpace Z] [MeasurableSingletonClass Z]
    {n : ℕ} (hn : 0 < n) (ω : Fin n → Z) (f : Z → ℝ) :
    WassersteinDRO.Duality.nominalRisk (MinimaxWass.DataDep.empiricalPM hn ω : Measure Z) f =
      (((1 / (n : ℝ)) * ∑ i : Fin n, f (ω i) : ℝ) : EReal) := by
  rw [nominalRisk_eq_integral _ f (integrable_empiricalPM hn ω f), integral_empiricalPM]

open WassVarReg.PInf in
lemma lower_bound {Z : Type*} [MetricSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    {n : ℕ} (hn : 0 < n) (ω : Fin n → Z) (f : Z → ℝ)
    (ρ : ℝ) (hρ : 0 ≤ ρ) (hG : ∀ i, Gf f ρ (ω i) ≠ ⊤) (ε : ℝ) (hε : 0 < ε) :
    (((1 / (n : ℝ)) * ∑ i : Fin n, (f (ω i) + (Gf f ρ (ω i)).toReal) - ε : ℝ) : EReal) ≤
      worstCaseInf ρ (MinimaxWass.DataDep.empiricalPM hn ω) f := by
  have hex : ∀ i, ∃ z', dist z' (ω i) ≤ ρ ∧
      (Gf f ρ (ω i)).toReal - ε < f z' - f (ω i) := by
    intro i
    have hlt : (((Gf f ρ (ω i)).toReal - ε : ℝ) : EReal) < Gf f ρ (ω i) := by
      rw [← Gf_coe f ρ hρ (ω i) (hG i)]
      exact_mod_cast (by linarith : (Gf f ρ (ω i)).toReal - ε < (Gf f ρ (ω i)).toReal)
    have hlt' := hlt
    unfold Gf at hlt'
    obtain ⟨z', hz'⟩ := lt_iSup_iff.1 hlt'
    obtain ⟨hd, hz''⟩ := lt_iSup_iff.1 hz'
    exact ⟨z', hd, by exact_mod_cast hz''⟩
  choose ω' hω'd hω'f using hex
  let P' := MinimaxWass.DataDep.empiricalPM hn ω'
  have hW : winfDist P' (MinimaxWass.DataDep.empiricalPM hn ω) ≤ ENNReal.ofReal ρ := by
    unfold winfDist
    let γ : Measure (Z × Z) :=
      (MinimaxWass.DataDep.empiricalPM hn (fun i => (ω' i, ω i)) : Measure (Z × Z))
    have hγ : γ ∈ WassersteinLinOpt.Ball.couplings (P' : Measure Z)
        (MinimaxWass.DataDep.empiricalPM hn ω : Measure Z) := by
      refine ⟨?_, ?_⟩
      · exact map_empiricalPM hn _ Prod.fst measurable_fst
      · exact map_empiricalPM hn _ Prod.snd measurable_snd
    refine (iInf₂_le γ hγ).trans ?_
    refine essSup_le_of_ae_le _ ?_
    filter_upwards [ae_mem_range_empiricalPM hn (fun i => (ω' i, ω i))] with x hx
    obtain ⟨i, rfl⟩ := hx
    exact ENNReal.ofReal_le_ofReal (hω'd i)
  refine le_trans ?_ (le_iSup₂ (f := fun (P : ProbabilityMeasure Z)
    (_ : winfDist P (MinimaxWass.DataDep.empiricalPM hn ω) ≤ ENNReal.ofReal ρ) =>
      WassersteinDRO.Duality.nominalRisk (P : Measure Z) f) P' hW)
  rw [nominalRisk_empiricalPM]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : ∑ i : Fin n, (f (ω i) + (Gf f ρ (ω i)).toReal - ε) ≤ ∑ i : Fin n, f (ω' i) :=
    Finset.sum_le_sum (fun i _ => by linarith [hω'f i])
  rw [Finset.sum_sub_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have : (1 / (n : ℝ)) * ∑ i : Fin n, (f (ω i) + (Gf f ρ (ω i)).toReal) - ε ≤
      (1 / (n : ℝ)) * ∑ i : Fin n, f (ω' i) := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, one_mul, one_mul, sub_le_iff_le_add,
      div_add' _ _ _ hn'.ne', div_le_div_iff_of_pos_right hn']
    linarith
  exact_mod_cast this


open WassVarReg.PInf in
lemma boundaryGap_le {Z : Type*} [MetricSpace Z] (D : Set Z) (z : Z) (ρ t : ℝ)
    (hρ : 0 ≤ ρ) (hρt : ρ ≤ t) :
    boundaryGap t D z ≤ boundaryGap ρ D z + (t - ρ) := by
  unfold boundaryGap
  have ht : ENNReal.ofReal t = ENNReal.ofReal ρ + ENNReal.ofReal (t - ρ) := by
    rw [← ENNReal.ofReal_add hρ (by linarith)]; congr 1; ring
  have h1 : ENNReal.ofReal t - Metric.infEDist z D ≤
      (ENNReal.ofReal ρ - Metric.infEDist z D) + ENNReal.ofReal (t - ρ) := by
    rw [ht, add_comm (ENNReal.ofReal ρ), add_comm _ (ENNReal.ofReal (t - ρ))]
    exact add_tsub_le_assoc
  have hfin : ENNReal.ofReal ρ - Metric.infEDist z D ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top tsub_le_self
  calc (ENNReal.ofReal t - Metric.infEDist z D).toReal
      ≤ ((ENNReal.ofReal ρ - Metric.infEDist z D) + ENNReal.ofReal (t - ρ)).toReal :=
        ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin, ENNReal.ofReal_ne_top⟩) h1
    _ = _ := by rw [ENNReal.toReal_add hfin ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal (by linarith)]

end WVR2Aux

open WVR2Aux WassVarReg.PInf

theorem solution {Z : Type*} [MetricSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] [SecondCountableTopology Z]
    (hnoiso : ∀ z : Z, (nhdsWithin z {z}ᶜ).NeBot)
    (F : Set (Z → ℝ)) (hmeas : ∀ f ∈ F, Measurable f)
    (D : (Z → ℝ) → Set Z) (H : Z → ℝ) (δ0 M : ℝ)
    (hδ0 : 0 < δ0) (hM : 0 ≤ M) (hA5 : Assumption5I F D H δ0 M) :
    ∃ ρbar : ℝ, 0 < ρbar ∧
      ∀ (n : ℕ) (hn : 0 < n) (ω : Fin n → Z) (ρ : ℝ),
        0 ≤ ρ → ρ < ρbar → ∀ f ∈ F,
          regularizerInf ρ (MinimaxWass.DataDep.empiricalPM hn ω) f ≠ ⊤ ∧
          regularizerInf ρ (MinimaxWass.DataDep.empiricalPM hn ω) f ≠ ⊥ ∧
          |(regularizerInf ρ (MinimaxWass.DataDep.empiricalPM hn ω) f).toReal -
            ρ * ((1 / (n : ℝ)) * ∑ i : Fin n, (localSlope f (ω i)).toReal)| ≤
            ρ ^ 2 * ((1 / (n : ℝ)) * ∑ i : Fin n, |H (ω i)|) +
              M * ((1 / (n : ℝ)) * ∑ i : Fin n, boundaryGap ρ (D f) (ω i)) := by
  refine ⟨δ0, hδ0, ?_⟩
  intro n hn ω ρ hρ hρδ f hfF
  have hf := hmeas f hfF
  have hA := hA5 f hfF
  have hGfin : ∀ t, 0 ≤ t → t < δ0 → ∀ i, Gf f t (ω i) ≠ ⊤ :=
    fun t h0 h1 i => ((hA (ω i)).2 t h0 h1).1
  have habs : ∀ t, 0 ≤ t → t < δ0 → ∀ i,
      |(Gf f t (ω i)).toReal - (localSlope f (ω i)).toReal * t| ≤
        H (ω i) * t ^ 2 + M * boundaryGap t (D f) (ω i) :=
    fun t h0 h1 i => ((hA (ω i)).2 t h0 h1).2
  have hup : ∀ t, ρ < t → t < δ0 →
      worstCaseInf ρ (MinimaxWass.DataDep.empiricalPM hn ω) f ≤
        (((1 / (n : ℝ)) * ∑ i : Fin n, (f (ω i) + (Gf f t (ω i)).toReal) : ℝ) : EReal) := by
    intro t hρt htδ
    unfold worstCaseInf
    refine iSup₂_le (fun P hP => ?_)
    unfold winfDist at hP
    have hlt := lt_of_le_of_lt hP ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hρt)
    obtain ⟨γ, hlt0⟩ := iInf_lt_iff.1 hlt
    obtain ⟨hγ, hlt'⟩ := iInf_lt_iff.1 hlt0
    refine upper_bound hn ω f hf P t (by linarith) γ hγ ?_ (hGfin t (by linarith) htδ)
    filter_upwards [ENNReal.ae_le_essSup (μ := γ) (fun x : Z × Z => ENNReal.ofReal (dist x.1 x.2))]
      with x hx
    exact (ENNReal.ofReal_le_ofReal_iff (by linarith)).1 (hx.trans hlt'.le)
  have hlow := lower_bound hn ω f ρ hρ (hGfin ρ hρ hρδ)
  set W := worstCaseInf ρ (MinimaxWass.DataDep.empiricalPM hn ω) f with hWdef
  have hWbot : W ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hlow 1 one_pos)
  have hWtop : W ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _)
    (hup ((ρ + δ0) / 2) (by linarith) (by linarith))
  set w := W.toReal with hwdef
  have hWw : W = (w : EReal) := (EReal.coe_toReal hWtop hWbot).symm
  set a := (1 / (n : ℝ)) * ∑ i : Fin n, f (ω i) with ha
  have hR : regularizerInf ρ (MinimaxWass.DataDep.empiricalPM hn ω) f = ((w - a : ℝ) : EReal) := by
    unfold regularizerInf
    rw [← hWdef, nominalRisk_empiricalPM, hWw, ← EReal.coe_sub]
  refine ⟨by rw [hR]; exact EReal.coe_ne_top _, by rw [hR]; exact EReal.coe_ne_bot _, ?_⟩
  rw [hR, EReal.toReal_coe]
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hN : (0 : ℝ) < 1 / (n : ℝ) := by positivity
  set N := 1 / (n : ℝ) with hNdef
  -- lower bound on w
  have hwl : N * ∑ i : Fin n, (f (ω i) + (Gf f ρ (ω i)).toReal) ≤ w := by
    by_contra hcon
    replace hcon := lt_of_not_ge hcon
    have := hlow ((N * ∑ i : Fin n, (f (ω i) + (Gf f ρ (ω i)).toReal) - w) / 2) (by linarith)
    rw [hWw] at this
    have := EReal.coe_le_coe_iff.1 this
    linarith
  have hwu : ∀ t, ρ < t → t < δ0 → w ≤ N * ∑ i : Fin n, (f (ω i) + (Gf f t (ω i)).toReal) := by
    intro t h1 h2
    have := hup t h1 h2
    rw [hWw] at this
    exact EReal.coe_le_coe_iff.1 this
  -- abbreviations
  set s : Fin n → ℝ := fun i => (localSlope f (ω i)).toReal with hs
  set g : ℝ → Fin n → ℝ := fun t i => boundaryGap t (D f) (ω i) with hg
  obtain ⟨kk, hkk⟩ : ∃ kk : Fin n → ℝ, ∀ i, kk i = s i + 2 * δ0 * |H (ω i)| + M :=
    ⟨_, fun i => rfl⟩
  have hkk0 : ∀ i, 0 ≤ kk i := by
    intro i; rw [hkk i]
    have : 0 ≤ s i := ENNReal.toReal_nonneg
    have : 0 ≤ |H (ω i)| := abs_nonneg _
    nlinarith
  -- per-sample lower
  have hLi : ∀ i, -(ρ ^ 2 * |H (ω i)| + M * g ρ i) ≤ (Gf f ρ (ω i)).toReal - ρ * s i := by
    intro i
    have h := (abs_le.1 (habs ρ hρ hρδ i)).1
    have : H (ω i) * ρ ^ 2 ≤ |H (ω i)| * ρ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg ρ)
    simp only [hs, hg]
    linarith
  -- per-sample upper
  have hUi : ∀ t, ρ < t → t < δ0 → ∀ i,
      (Gf f t (ω i)).toReal - ρ * s i ≤ ρ ^ 2 * |H (ω i)| + M * g ρ i + (t - ρ) * kk i := by
    intro t h1 h2 i
    have h := (abs_le.1 (habs t (by linarith) h2 i)).2
    have htsq : t ^ 2 ≤ ρ ^ 2 + 2 * δ0 * (t - ρ) := by nlinarith
    have hH : H (ω i) * t ^ 2 ≤ |H (ω i)| * (ρ ^ 2 + 2 * δ0 * (t - ρ)) :=
      (mul_le_mul_of_nonneg_right (le_abs_self _) (sq_nonneg t)).trans
        (mul_le_mul_of_nonneg_left htsq (abs_nonneg _))
    have hgap : M * boundaryGap t (D f) (ω i) ≤ M * (g ρ i + (t - ρ)) :=
      mul_le_mul_of_nonneg_left (boundaryGap_le _ _ ρ t hρ h1.le) hM
    rw [hkk i]
    simp only [hs, hg] at *
    nlinarith
  -- summed lower
  have hL : N * ∑ i : Fin n, (-(ρ ^ 2 * |H (ω i)| + M * g ρ i)) ≤
      N * ∑ i : Fin n, ((Gf f ρ (ω i)).toReal - ρ * s i) :=
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hLi i) hN.le
  have hU : ∀ t, ρ < t → t < δ0 →
      N * ∑ i : Fin n, ((Gf f t (ω i)).toReal - ρ * s i) ≤
        N * ∑ i : Fin n, (ρ ^ 2 * |H (ω i)| + M * g ρ i + (t - ρ) * kk i) :=
    fun t h1 h2 => mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hUi t h1 h2 i) hN.le
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
    ← Finset.mul_sum] at hL hU hwl hwu
  have hK : 0 ≤ N * ∑ i : Fin n, kk i :=
    mul_nonneg hN.le (Finset.sum_nonneg fun i _ => hkk0 i)
  set K := N * ∑ i : Fin n, kk i with hKdef
  rw [abs_le]
  constructor
  · simp only [hs, hg] at hL hwl
    nlinarith
  · by_contra hcon
    replace hcon := lt_of_not_ge hcon
    set E := ρ ^ 2 * (N * ∑ i, |H (ω i)|) + M * (N * ∑ i, boundaryGap ρ (D f) (ω i)) with hE
    set d := w - a - ρ * (N * Finset.univ.sum s) - E with hd
    have hd0 : 0 < d := by rw [hd]; linarith
    set u := min ((δ0 - ρ) / 2) (d / (2 * (K + 1))) with hu
    have hu0 : 0 < u := lt_min (by linarith) (by positivity)
    have hu1 : u ≤ (δ0 - ρ) / 2 := min_le_left _ _
    have hu2 : u ≤ d / (2 * (K + 1)) := min_le_right _ _
    have ht1 : ρ < ρ + u := by linarith
    have ht2 : ρ + u < δ0 := by linarith
    have key := hU (ρ + u) ht1 ht2
    have key2 := hwu (ρ + u) ht1 ht2
    simp only [hg] at key
    have hmain : w - a - ρ * (N * Finset.univ.sum s) ≤ E + u * K := by
      rw [hKdef, hE, ha]
      have e1 : ρ + u - ρ = u := by ring
      rw [e1] at key
      linear_combination key + key2
    have h3 : u * K ≤ d / (2 * (K + 1)) * K := mul_le_mul_of_nonneg_right hu2 hK
    have h4 : d / (2 * (K + 1)) * K < d := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
