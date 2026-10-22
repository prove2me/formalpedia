-- Prove2me | solution 1 for ReedGGN.RenewalRep.exponential_service
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T05:17:34.400155+00:00
-- url     : https://prove2.me/submissions/0f9ee508-0c8e-48f9-bd2e-6a24d78aa0ec

import Mathlib
import Definitions.Def_ReedGGN_RenewalRep_Basic
import Definitions.Def_ReedGGN_RenewalRep_RenewalFunction
import Definitions.Def_ReedGGN_RenewalRep_Equations

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace ReedGGN.RenewalRep

lemma g46_convPow_prob (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ∀ n, IsProbabilityMeasure (convPow μ n) := by
  intro n
  induction n with
  | zero => simp only [convPow]; infer_instance
  | succ n ih =>
    simp only [convPow, Measure.conv]
    exact Measure.isProbabilityMeasure_map (measurable_add.aemeasurable)

lemma g46_conv_carried (ν μ : Measure ℝ) [SFinite μ] [SFinite ν] (hν : ν (Set.Iio 0) = 0)
    (hμ : μ (Set.Iio 0) = 0) : (ν.conv μ) (Set.Iio 0) = 0 := by
  rw [Measure.conv, Measure.map_apply measurable_add measurableSet_Iio]
  apply measure_mono_null (t := (Set.Iio 0 ×ˢ Set.univ) ∪ (Set.univ ×ˢ Set.Iio 0))
  · intro p hp
    simp only [Set.mem_preimage, Set.mem_Iio] at hp
    by_cases h : p.1 < 0
    · left; exact ⟨h, trivial⟩
    · right; refine ⟨trivial, ?_⟩; simp only [Set.mem_Iio]; linarith
  · apply measure_union_null
    · rw [Measure.prod_prod, hν, zero_mul]
    · rw [Measure.prod_prod, hμ, mul_zero]

lemma g46_convPow_carried (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ0 : μ (Set.Iio 0) = 0) :
    ∀ n, convPow μ n (Set.Iio 0) = 0 := by
  intro n
  induction n with
  | zero => simp [convPow]
  | succ n ih =>
    haveI := g46_convPow_prob μ n
    simp only [convPow]
    exact g46_conv_carried _ _ ih hμ0

lemma g46_rm_carried (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ0 : μ (Set.Iio 0) = 0) :
    renewalMeasure μ (Set.Iio 0) = 0 := by
  rw [renewalMeasure, Measure.sum_apply _ measurableSet_Iio]
  simp [g46_convPow_carried μ hμ0]

instance g46_rm_sfinite (μ : Measure ℝ) [IsProbabilityMeasure μ] : SFinite (renewalMeasure μ) := by
  haveI := g46_convPow_prob μ
  unfold renewalMeasure; infer_instance

lemma g46_Iic_eq_Icc (ν : Measure ℝ) (hν : ν (Set.Iio 0) = 0) (s : ℝ) :
    ν (Set.Iic s) = ν (Set.Icc 0 s) := by
  apply le_antisymm
  · calc ν (Set.Iic s) ≤ ν (Set.Iio 0 ∪ Set.Icc 0 s) := by
          apply measure_mono; intro x hx
          by_cases h : x < 0
          · left; exact h
          · right; exact ⟨not_lt.mp h, hx⟩
      _ ≤ ν (Set.Iio 0) + ν (Set.Icc 0 s) := measure_union_le _ _
      _ = ν (Set.Icc 0 s) := by rw [hν, zero_add]
  · exact measure_mono Set.Icc_subset_Iic_self

/-- M1 : dM = μ + dM ∗ μ -/
lemma g46_rm_eq (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    renewalMeasure μ = μ + (renewalMeasure μ).conv μ := by
  haveI := g46_convPow_prob μ
  ext s hs
  have h1 : ((renewalMeasure μ).conv μ) s = ∑' n, convPow μ (n + 2) s := by
    rw [← lintegral_indicator_one hs, Measure.lintegral_conv (measurable_one.indicator hs)]
    rw [renewalMeasure, lintegral_sum_measure]
    congr 1; funext n
    rw [show convPow μ (n + 2) = (convPow μ (n + 1)).conv μ from rfl, ← lintegral_indicator_one hs,
      Measure.lintegral_conv (measurable_one.indicator hs)]
  rw [Measure.add_apply, h1, renewalMeasure, Measure.sum_apply _ hs]
  rw [tsum_eq_zero_add' ENNReal.summable]
  have h0 : convPow μ (0 + 1) = μ := by
    simp only [convPow]
    rw [Measure.dirac_conv]; simp
  rw [h0]

lemma g46_exists_delta (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ0 : μ (Set.Iio 0) = 0)
    (hatom : μ {0} < 1) : ∃ δ : ℝ, 0 < δ ∧ 0 < μ (Set.Ioi δ) := by
  have hI : μ (Set.Iic 0) < 1 := by
    rw [g46_Iic_eq_Icc μ hμ0, Set.Icc_self]; exact hatom
  have hpos : 0 < μ (Set.Ioi 0) := by
    have := prob_compl_eq_one_sub (μ := μ) (measurableSet_Iic (a := (0:ℝ)))
    rw [Set.compl_Iic] at this
    rw [this]; exact tsub_pos_of_lt hI
  by_contra hne
  push_neg at hne
  have : μ (Set.Ioi 0) = 0 := by
    have hU : Set.Ioi (0:ℝ) = ⋃ n : ℕ, Set.Ioi (1 / ((n:ℝ) + 1)) := by
      ext x; simp only [Set.mem_Ioi, Set.mem_iUnion]
      constructor
      · intro hx; obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx; exact ⟨n, hn⟩
      · rintro ⟨n, hn⟩; exact lt_trans (by positivity) hn
    rw [hU, measure_iUnion_null_iff]
    intro n; exact le_antisymm (hne _ (by positivity)) bot_le
  exact absurd this hpos.ne'

lemma g46_laplace (μ : Measure ℝ) [IsProbabilityMeasure μ] (n : ℕ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (-x)) ∂(convPow μ n)
      = (∫⁻ x, ENNReal.ofReal (Real.exp (-x)) ∂μ) ^ n := by
  have hm : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (-x)) := by fun_prop
  induction n with
  | zero => simp [convPow, lintegral_dirac' _ hm]
  | succ n ih =>
    haveI := g46_convPow_prob μ n
    rw [show convPow μ (n + 1) = (convPow μ n).conv μ from rfl, Measure.lintegral_conv hm]
    have : ∀ x : ℝ, ∫⁻ y, ENNReal.ofReal (Real.exp (-(x + y))) ∂μ
        = ENNReal.ofReal (Real.exp (-x)) * ∫⁻ y, ENNReal.ofReal (Real.exp (-y)) ∂μ := by
      intro x
      rw [← lintegral_const_mul _ hm]
      congr 1; funext y
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; ring_nf
    simp_rw [this]
    rw [lintegral_mul_const _ hm, ih, pow_succ]

lemma g46_phi_lt_one (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ0 : μ (Set.Iio 0) = 0)
    (hatom : μ {0} < 1) : ∫⁻ x, ENNReal.ofReal (Real.exp (-x)) ∂μ < 1 := by
  obtain ⟨δ, hδ, hμδ⟩ := g46_exists_delta μ hμ0 hatom
  set a := ENNReal.ofReal (Real.exp (-δ)) with ha
  have ha1 : a < 1 := by
    rw [ha, ENNReal.ofReal_lt_one]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hle : ∀ᵐ x ∂μ, ENNReal.ofReal (Real.exp (-x)) ≤ (Set.Ioi δ).indicator (fun _ => a) x
      + (Set.Iic δ).indicator (fun _ => 1) x := by
    have h0 : ∀ᵐ x ∂μ, 0 ≤ x := by
      rw [ae_iff]
      have : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext; simp
      rw [this]; exact hμ0
    filter_upwards [h0] with x hx
    by_cases h : δ < x
    · have : x ∉ Set.Iic δ := by simpa using h
      rw [Set.indicator_of_mem (show x ∈ Set.Ioi δ from h), Set.indicator_of_notMem this, add_zero, ha]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))
    · have : x ∈ Set.Iic δ := by simpa using h
      rw [Set.indicator_of_notMem (show x ∉ Set.Ioi δ by simpa using h), Set.indicator_of_mem this, zero_add]
      rw [ENNReal.ofReal_le_one]; exact Real.exp_le_one_iff.mpr (by linarith)
  calc ∫⁻ x, ENNReal.ofReal (Real.exp (-x)) ∂μ
      ≤ ∫⁻ x, ((Set.Ioi δ).indicator (fun _ => a) x + (Set.Iic δ).indicator (fun _ => 1) x) ∂μ :=
        lintegral_mono_ae hle
    _ = a * μ (Set.Ioi δ) + μ (Set.Iic δ) := by
        rw [lintegral_add_left ((measurable_const).indicator measurableSet_Ioi),
          lintegral_indicator measurableSet_Ioi, lintegral_indicator measurableSet_Iic]
        simp
    _ < μ (Set.Ioi δ) + μ (Set.Iic δ) := by
        apply ENNReal.add_lt_add_right (measure_ne_top _ _)
        calc a * μ (Set.Ioi δ) < 1 * μ (Set.Ioi δ) :=
              ENNReal.mul_lt_mul_left hμδ.ne' (measure_ne_top _ _) ha1
          _ = μ (Set.Ioi δ) := one_mul _
    _ = 1 := by
        rw [add_comm, ← measure_union ?_ measurableSet_Ioi]
        · rw [Set.Iic_union_Ioi]; simp
        · exact Set.disjoint_left.mpr fun x h1 h2 => by simp at h1 h2; linarith

lemma g46_tsum_fin (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ0 : μ (Set.Iio 0) = 0)
    (hatom : μ {0} < 1) (t : ℝ) : ∑' n, convPow μ n (Set.Iic t) ≠ ⊤ := by
  set φ := ∫⁻ x, ENNReal.ofReal (Real.exp (-x)) ∂μ
  have hφ := g46_phi_lt_one μ hμ0 hatom
  have hb : ∀ n, convPow μ n (Set.Iic t) ≤ ENNReal.ofReal (Real.exp t) * φ ^ n := by
    intro n
    rw [← g46_laplace, ← lintegral_const_mul _ (by fun_prop), ← lintegral_indicator_one measurableSet_Iic]
    apply lintegral_mono
    intro x
    by_cases hx : x ∈ Set.Iic t
    · rw [Set.indicator_of_mem hx]
      show (1:ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp t) * ENNReal.ofReal (Real.exp (-x))
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      rw [ENNReal.one_le_ofReal]; apply Real.one_le_exp; simp at hx; linarith
    · rw [Set.indicator_of_notMem hx]; exact bot_le
  apply ne_top_of_le_ne_top _ (ENNReal.tsum_le_tsum hb)
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
  exact ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hφ).ne'

lemma g46_rm_fin (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ0 : μ (Set.Iio 0) = 0)
    (hatom : μ {0} < 1) (t : ℝ) : renewalMeasure μ (Set.Iic t) < ⊤ := by
  rw [renewalMeasure, Measure.sum_apply _ measurableSet_Iic, lt_top_iff_ne_top]
  apply ne_top_of_le_ne_top (g46_tsum_fin μ hμ0 hatom t)
  rw [tsum_eq_zero_add' ENNReal.summable (f := fun n => convPow μ n (Set.Iic t))]
  exact le_add_self

lemma g46_tail_tendsto (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ0 : μ (Set.Iio 0) = 0)
    (hatom : μ {0} < 1) (t : ℝ) :
    Tendsto (fun n => (convPow μ n (Set.Iic t)).toReal) atTop (𝓝 0) := by
  have := ENNReal.tendsto_atTop_zero_of_tsum_ne_top (g46_tsum_fin μ hμ0 hatom t)
  have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp this
  simp only [ENNReal.toReal_zero] at h2; exact h2

lemma g46_atom_of_mean (μ : Measure ℝ) [IsProbabilityMeasure μ] (hmean : ∫ x, x ∂μ = 1) :
    μ {0} < 1 := by
  by_contra h
  push_neg at h
  have h1 : μ {0} = 1 := le_antisymm prob_le_one h
  have hae : ∀ᵐ x ∂μ, x = 0 := by
    rw [ae_iff]
    have := (prob_compl_eq_zero_iff (μ := μ) (measurableSet_singleton (0:ℝ))).mpr h1
    simpa [Set.compl_def] using this
  have : ∫ x, x ∂μ = 0 := by
    rw [integral_congr_ae hae]; simp
  rw [this] at hmean; exact zero_ne_one hmean

lemma g46_ae_nonneg (ν : Measure ℝ) (h : ν (Set.Iio 0) = 0) : ∀ᵐ x ∂ν, 0 ≤ x := by
  rw [ae_iff]
  have : {a : ℝ | ¬ 0 ≤ a} = Set.Iio 0 := by ext; simp
  rw [this]; exact h

lemma g46_intOn (ν : Measure ℝ) {t C : ℝ} (hfin : ν (Set.Icc 0 t) < ⊤) {f : ℝ → ℝ}
    (hf : Measurable f) (hC : ∀ s ∈ Set.Icc 0 t, |f s| ≤ C) :
    IntegrableOn (fun u => f (t - u)) (Set.Icc 0 t) ν := by
  haveI : IsFiniteMeasure (ν.restrict (Set.Icc 0 t)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  refine Integrable.of_bound (hf.comp (measurable_const.sub measurable_id)).aestronglyMeasurable C ?_
  refine ae_restrict_of_forall_mem measurableSet_Icc ?_
  intro u hu
  rw [Real.norm_eq_abs]; apply hC; constructor <;> linarith [hu.1, hu.2]

lemma g46_K_bound (ν : Measure ℝ) {t C : ℝ} (hfin : ν (Set.Icc 0 t) < ⊤) {f : ℝ → ℝ}
    (hC : ∀ s ∈ Set.Icc 0 t, |f s| ≤ C) :
    |∫ u in Set.Icc 0 t, f (t - u) ∂ν| ≤ C * (ν (Set.Icc 0 t)).toReal := by
  have := norm_setIntegral_le_of_norm_le_const hfin (f := fun u => f (t - u)) (C := C)
    (fun u hu => by rw [Real.norm_eq_abs]; apply hC; constructor <;> linarith [hu.1, hu.2])
  simpa [Real.norm_eq_abs, Measure.real] using this

lemma g46_K_meas (ν : Measure ℝ) [SFinite ν] {f : ℝ → ℝ} (hf : Measurable f) :
    Measurable (fun t => ∫ u in Set.Icc 0 t, f (t - u) ∂ν) := by
  have hS : MeasurableSet {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1} :=
    (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst)
  have hF : StronglyMeasurable
      (({p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1}).indicator (fun p => f (p.1 - p.2))) := by
    apply Measurable.stronglyMeasurable
    exact (hf.comp (measurable_fst.sub measurable_snd)).indicator hS
  have := hF.integral_prod_right' (ν := ν)
  convert this.measurable using 1
  funext t
  rw [← integral_indicator measurableSet_Icc]
  congr 1

lemma g46_K_add (μ ρ : Measure ℝ) {t : ℝ} {f : ℝ → ℝ}
    (h1 : IntegrableOn (fun u => f (t - u)) (Set.Icc 0 t) μ)
    (h2 : IntegrableOn (fun u => f (t - u)) (Set.Icc 0 t) ρ) :
    ∫ u in Set.Icc 0 t, f (t - u) ∂(μ + ρ)
      = ∫ u in Set.Icc 0 t, f (t - u) ∂μ + ∫ u in Set.Icc 0 t, f (t - u) ∂ρ := by
  rw [Measure.restrict_add]; exact integral_add_measure h1 h2

lemma g46_conv_fin (ν μ : Measure ℝ) [SFinite ν] [IsFiniteMeasure μ] (hν0 : ν (Set.Iio 0) = 0)
    (hμ0 : μ (Set.Iio 0) = 0) (t : ℝ) (hνt : ν (Set.Iic t) < ⊤) :
    (ν.conv μ) (Set.Icc 0 t) < ⊤ := by
  rw [Measure.conv, Measure.map_apply measurable_add measurableSet_Icc]
  calc (ν.prod μ) ((fun x : ℝ × ℝ => x.1 + x.2) ⁻¹' Set.Icc 0 t)
      ≤ (ν.prod μ) ((Set.Iio 0 ×ˢ Set.univ) ∪ (Set.univ ×ˢ Set.Iio 0) ∪
          (Set.Iic t ×ˢ Set.univ)) := by
        apply measure_mono; intro p hp
        simp only [Set.mem_preimage, Set.mem_Icc] at hp
        by_cases h1 : p.1 < 0
        · left; left; exact ⟨h1, trivial⟩
        by_cases h2 : p.2 < 0
        · left; right; exact ⟨trivial, h2⟩
        right; refine ⟨?_, trivial⟩; simp only [Set.mem_Iic]; linarith
    _ ≤ (ν.prod μ) (Set.Iio 0 ×ˢ Set.univ) + (ν.prod μ) (Set.univ ×ˢ Set.Iio 0) +
          (ν.prod μ) (Set.Iic t ×ˢ Set.univ) := by
        refine (measure_union_le _ _).trans ?_; gcongr; exact measure_union_le _ _
    _ < ⊤ := by
        rw [Measure.prod_prod, Measure.prod_prod, Measure.prod_prod, hν0, hμ0]
        simp only [zero_mul, mul_zero, zero_add]
        exact ENNReal.mul_lt_top hνt (measure_lt_top _ _)

lemma g46_K_conv (ν μ : Measure ℝ) [SFinite ν] [IsFiniteMeasure μ] (hν0 : ν (Set.Iio 0) = 0)
    (hμ0 : μ (Set.Iio 0) = 0) (hνfin : ∀ s, ν (Set.Iic s) < ⊤) {f : ℝ → ℝ} (hf : Measurable f)
    {t C : ℝ} (hC : ∀ s ∈ Set.Icc 0 t, |f s| ≤ C) :
    ∫ u in Set.Icc 0 t, f (t - u) ∂(ν.conv μ)
      = ∫ u in Set.Icc 0 t, (∫ v in Set.Icc 0 (t - u), f (t - u - v) ∂ν) ∂μ := by
  have hgint : Integrable ((Set.Icc 0 t).indicator (fun u => f (t - u))) (μ.conv ν) := by
    rw [integrable_indicator_iff measurableSet_Icc, Measure.conv_comm]
    exact g46_intOn _ (g46_conv_fin ν μ hν0 hμ0 t (hνfin t)) hf hC
  rw [← integral_indicator measurableSet_Icc, Measure.conv_comm, integral_conv hgint]
  have hin : ∀ u, 0 ≤ u → ∫ v, (Set.Icc 0 t).indicator (fun u => f (t - u)) (u + v) ∂ν
      = ∫ v in Set.Icc 0 (t - u), f (t - u - v) ∂ν := by
    intro u hu
    rw [← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards [g46_ae_nonneg ν hν0] with v hv
    by_cases h : v ≤ t - u
    · rw [Set.indicator_of_mem (show u + v ∈ Set.Icc 0 t from ⟨by linarith, by linarith⟩),
        Set.indicator_of_mem (show v ∈ Set.Icc 0 (t - u) from ⟨hv, h⟩)]
      ring_nf
    · rw [Set.indicator_of_notMem (show u + v ∉ Set.Icc 0 t from fun hm => h (by linarith [hm.2])),
        Set.indicator_of_notMem (show v ∉ Set.Icc 0 (t - u) from fun hm => h hm.2)]
  rw [integral_congr_ae (g := fun u => ∫ v in Set.Icc 0 (t - u), f (t - u - v) ∂ν)]
  · symm
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [g46_ae_nonneg μ hμ0] with u hu hnot
    have : t < u := by
      by_contra hc; exact hnot ⟨hu, not_lt.mp hc⟩
    rw [Set.Icc_eq_empty (by linarith), Measure.restrict_empty, integral_zero_measure]
  · filter_upwards [g46_ae_nonneg μ hμ0] with u hu
    exact hin u hu

lemma g46_uniq (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ0 : μ (Set.Iio 0) = 0)
    (hatom : μ {0} < 1) (d : ℝ → ℝ) (hdm : Measurable d) (hdb : IsLocallyBounded d)
    (hd : ∀ t, 0 ≤ t → |d t| ≤ ∫ u in Set.Icc 0 t, |d (t - u)| ∂μ) :
    ∀ t, 0 ≤ t → d t = 0 := by
  intro T hT
  obtain ⟨C, hC⟩ := hdb T hT
  have key : ∀ n : ℕ, ∀ t ∈ Set.Icc 0 T, |d t| ≤ C * (convPow μ n (Set.Iic t)).toReal := by
    intro n
    induction n with
    | zero =>
      intro t ht
      have : (convPow μ 0 (Set.Iic t)).toReal = 1 := by
        simp [convPow, ht.1]
      rw [this, mul_one]; exact hC t ht
    | succ n ih =>
      intro t ht
      haveI := g46_convPow_prob μ n
      have hcv := g46_K_conv (convPow μ n) μ (g46_convPow_carried μ hμ0 n) hμ0
        (fun s => measure_lt_top _ _) (f := fun _ => (1:ℝ)) measurable_const (t := t) (C := 1)
        (fun s _ => by simp)
      simp only [integral_const, smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply_univ] at hcv
      have hanti : Antitone fun u => (convPow μ n (Set.Iic (t - u))).toReal := by
        intro a b hab
        apply ENNReal.toReal_mono (measure_ne_top _ _)
        apply measure_mono; intro x hx; simp only [Set.mem_Iic] at hx ⊢; linarith
      have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0 ⟨le_rfl, hT⟩)
      calc |d t| ≤ ∫ u in Set.Icc 0 t, |d (t - u)| ∂μ := hd t ht.1
        _ ≤ ∫ u in Set.Icc 0 t, C * (convPow μ n (Set.Iic (t - u))).toReal ∂μ := by
          apply setIntegral_mono_on
          · exact g46_intOn μ (measure_lt_top _ _) (f := fun s => |d s|) hdm.abs
              (C := C) (fun s hs => by rw [abs_abs]; exact hC s ⟨hs.1, hs.2.trans ht.2⟩)
          · refine Integrable.of_bound ((hanti.measurable.const_mul C).aestronglyMeasurable) C ?_
            refine Eventually.of_forall (fun u => ?_)
            rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC0 ENNReal.toReal_nonneg)]
            have : (convPow μ n (Set.Iic (t - u))).toReal ≤ 1 := by
              exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
            nlinarith
          · exact measurableSet_Icc
          · intro u hu
            exact ih (t - u) ⟨by linarith [hu.2], by linarith [hu.1, ht.2]⟩
        _ = C * (convPow μ (n + 1) (Set.Iic t)).toReal := by
          rw [integral_const_mul]
          congr 1
          have e1 : ∀ s, convPow μ n (Set.Iic s) = convPow μ n (Set.Icc 0 s) :=
            g46_Iic_eq_Icc _ (g46_convPow_carried μ hμ0 n)
          simp_rw [e1]
          rw [g46_Iic_eq_Icc _ (g46_convPow_carried μ hμ0 (n + 1))]
          exact hcv.symm
  have hlim := (g46_tail_tendsto μ hμ0 hatom T).const_mul C
  rw [mul_zero] at hlim
  have : |d T| ≤ 0 := ge_of_tendsto' hlim (fun n => key n T ⟨hT, le_rfl⟩)
  exact abs_nonpos_iff.mp this

lemma g46_rm_fin_Icc (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ0 : μ (Set.Iio 0) = 0)
    (hatom : μ {0} < 1) (s : ℝ) : renewalMeasure μ (Set.Icc 0 s) < ⊤ :=
  (measure_mono Set.Icc_subset_Iic_self).trans_lt (g46_rm_fin μ hμ0 hatom s)

lemma g46_KdM_split (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ0 : μ (Set.Iio 0) = 0)
    (hatom : μ {0} < 1) {f : ℝ → ℝ} (hf : Measurable f) {t C : ℝ}
    (hC : ∀ s ∈ Set.Icc 0 t, |f s| ≤ C) :
    ∫ u in Set.Icc 0 t, f (t - u) ∂(renewalMeasure μ)
      = ∫ u in Set.Icc 0 t, f (t - u) ∂μ
        + ∫ u in Set.Icc 0 t, (∫ v in Set.Icc 0 (t - u), f (t - u - v) ∂(renewalMeasure μ)) ∂μ := by
  have hint : IntegrableOn (fun u => f (t - u)) (Set.Icc 0 t) (renewalMeasure μ) :=
    g46_intOn _ (g46_rm_fin_Icc μ hμ0 hatom t) hf hC
  have e : ∫ u in Set.Icc 0 t, f (t - u) ∂(renewalMeasure μ)
      = ∫ u in Set.Icc 0 t, f (t - u) ∂(μ + (renewalMeasure μ).conv μ) := by
    rw [← g46_rm_eq μ]
  rw [e]
  rw [g46_rm_eq μ] at hint
  have hint' := integrableOn_add_measure.mp hint
  rw [g46_K_add _ _ hint'.1 hint'.2]
  congr 1
  exact g46_K_conv (renewalMeasure μ) μ (g46_rm_carried μ hμ0) hμ0 (g46_rm_fin μ hμ0 hatom) hf hC

lemma g46_uniq_lin (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ0 : μ (Set.Iio 0) = 0)
    (hatom : μ {0} < 1) (H r1 r2 : ℝ → ℝ) (h1m : Measurable r1) (h1b : IsLocallyBounded r1)
    (h2m : Measurable r2) (h2b : IsLocallyBounded r2)
    (h1 : ∀ t, 0 ≤ t → r1 t = H t + ∫ u in Set.Icc 0 t, r1 (t - u) ∂μ)
    (h2 : ∀ t, 0 ≤ t → r2 t = H t + ∫ u in Set.Icc 0 t, r2 (t - u) ∂μ) :
    Set.EqOn r1 r2 (Set.Ici 0) := by
  intro t ht
  have := g46_uniq μ hμ0 hatom (fun s => r1 s - r2 s) (h1m.sub h2m) ?_ ?_ t ht
  · simpa [sub_eq_zero] using this
  · intro T hT; obtain ⟨C1, hC1⟩ := h1b T hT; obtain ⟨C2, hC2⟩ := h2b T hT
    exact ⟨C1 + C2, fun s hs => (abs_sub _ _).trans (add_le_add (hC1 s hs) (hC2 s hs))⟩
  · intro s hs
    obtain ⟨C1, hC1⟩ := h1b s hs; obtain ⟨C2, hC2⟩ := h2b s hs
    have i1 := g46_intOn μ (measure_lt_top _ _) h1m hC1
    have i2 := g46_intOn μ (measure_lt_top _ _) h2m hC2
    have : r1 s - r2 s = ∫ u in Set.Icc 0 s, (r1 (s - u) - r2 (s - u)) ∂μ := by
      rw [integral_sub i1 i2]
      rw [h1 s hs, h2 s hs]; ring
    rw [this]; exact abs_integral_le_integral_abs

theorem g46_rte (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hatom : μ {0} < 1)
    (H : ℝ → ℝ) (hHm : Measurable H) (hHb : IsLocallyBounded H) :
    let r : ℝ → ℝ := fun t => H t + ∫ u in Set.Icc 0 t, H (t - u) ∂(renewalMeasure μ)
    IsLocallyBounded r ∧
    (∀ t : ℝ, 0 ≤ t → r t = H t + ∫ u in Set.Icc 0 t, r (t - u) ∂μ) ∧
    (∀ r' : ℝ → ℝ, Measurable r' → IsLocallyBounded r' →
      (∀ t : ℝ, 0 ≤ t → r' t = H t + ∫ u in Set.Icc 0 t, r' (t - u) ∂μ) →
      Set.EqOn r' r (Set.Ici 0)) := by
  intro r
  have hrb : IsLocallyBounded r := by
    intro T hT
    obtain ⟨C, hC⟩ := hHb T hT
    refine ⟨C + C * (renewalMeasure μ (Set.Iic T)).toReal, fun t ht => ?_⟩
    have h1 := g46_K_bound (renewalMeasure μ) (g46_rm_fin_Icc μ hμ0 hatom t) (f := H) (C := C)
      (fun s hs => hC s ⟨hs.1, hs.2.trans ht.2⟩)
    have h2 : (renewalMeasure μ (Set.Icc 0 t)).toReal ≤ (renewalMeasure μ (Set.Iic T)).toReal :=
      ENNReal.toReal_mono (g46_rm_fin μ hμ0 hatom T).ne
        (measure_mono (Set.Icc_subset_Iic_self.trans (Set.Iic_subset_Iic.mpr ht.2)))
    have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC t ht)
    calc |r t| ≤ |H t| + |∫ u in Set.Icc 0 t, H (t - u) ∂(renewalMeasure μ)| := abs_add_le _ _
      _ ≤ C + C * (renewalMeasure μ (Set.Iic T)).toReal :=
          add_le_add (hC t ht) (h1.trans (mul_le_mul_of_nonneg_left h2 hC0))
  have hrm : Measurable r := hHm.add (g46_K_meas _ hHm)
  have heq : ∀ t, 0 ≤ t → r t = H t + ∫ u in Set.Icc 0 t, r (t - u) ∂μ := by
    intro t ht
    obtain ⟨C, hC⟩ := hHb t ht
    have hsplit := g46_KdM_split μ hμ0 hatom hHm hC
    have i1 := g46_intOn μ (measure_lt_top _ _) hHm hC
    have hKm := g46_K_meas (renewalMeasure μ) hHm
    obtain ⟨D, hD⟩ := hrb t ht
    have hKb : ∀ s ∈ Set.Icc 0 t,
        |(fun s => ∫ u in Set.Icc 0 s, H (s - u) ∂(renewalMeasure μ)) s| ≤ C * (renewalMeasure μ (Set.Iic t)).toReal := by
      intro s hs
      have h1 := g46_K_bound (renewalMeasure μ) (g46_rm_fin_Icc μ hμ0 hatom s) (f := H) (C := C)
        (fun x hx => hC x ⟨hx.1, hx.2.trans hs.2⟩)
      have h2 : (renewalMeasure μ (Set.Icc 0 s)).toReal ≤ (renewalMeasure μ (Set.Iic t)).toReal :=
        ENNReal.toReal_mono (g46_rm_fin μ hμ0 hatom t).ne
          (measure_mono (Set.Icc_subset_Iic_self.trans (Set.Iic_subset_Iic.mpr hs.2)))
      have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC t ⟨ht, le_rfl⟩)
      exact h1.trans (mul_le_mul_of_nonneg_left h2 hC0)
    have i2 := g46_intOn μ (measure_lt_top _ _) hKm hKb
    have hlin : ∫ u in Set.Icc 0 t, r (t - u) ∂μ = ∫ u in Set.Icc 0 t, H (t - u) ∂μ
        + ∫ u in Set.Icc 0 t, (∫ v in Set.Icc 0 (t - u), H (t - u - v) ∂(renewalMeasure μ)) ∂μ := by
      rw [← integral_add i1 i2]
    show H t + ∫ u in Set.Icc 0 t, H (t - u) ∂(renewalMeasure μ) = _
    rw [hlin, hsplit]
  refine ⟨hrb, heq, fun r' hr'm hr'b hr' => ?_⟩
  exact g46_uniq_lin μ hμ0 hatom H r' r hr'm hr'b hrm hrb hr' heq

lemma g46_M_mono (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ0 : μ (Set.Iio 0) = 0)
    (hatom : μ {0} < 1) : Monotone (renewalFn μ) := by
  intro a b hab
  exact ENNReal.toReal_mono (g46_rm_fin μ hμ0 hatom b).ne (measure_mono (Set.Iic_subset_Iic.mpr hab))

theorem g46_re_core (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hatom : μ {0} < 1) :
    (∀ t : ℝ, renewalMeasure μ (Set.Iic t) < ⊤) ∧
    (∀ t : ℝ, 0 ≤ t →
      renewalFn μ t = cdf μ t + ∫ u in Set.Icc 0 t, renewalFn μ (t - u) ∂μ) ∧
    (∀ m : ℝ → ℝ, Measurable m → IsLocallyBounded m →
      (∀ t : ℝ, 0 ≤ t → m t = cdf μ t + ∫ u in Set.Icc 0 t, m (t - u) ∂μ) →
      Set.EqOn m (renewalFn μ) (Set.Ici 0)) := by
  have hM : ∀ s, (∫ v in Set.Icc 0 s, (1:ℝ) ∂(renewalMeasure μ)) = renewalFn μ s := by
    intro s; simp [Measure.real, renewalFn, g46_Iic_eq_Icc _ (g46_rm_carried μ hμ0)]
  have heq : ∀ t, 0 ≤ t →
      renewalFn μ t = cdf μ t + ∫ u in Set.Icc 0 t, renewalFn μ (t - u) ∂μ := by
    intro t ht
    have hs := g46_KdM_split μ hμ0 hatom (f := fun _ => (1:ℝ)) measurable_const (t := t) (C := 1)
      (fun s _ => by simp)
    beta_reduce at hs
    simp only [hM] at hs
    have e1 : cdf μ t = ∫ u in Set.Icc 0 t, (1:ℝ) ∂μ := by
      rw [cdf_eq_real]; simp [Measure.real, g46_Iic_eq_Icc _ hμ0]
    rw [e1]; exact hs
  have hMm : Measurable (renewalFn μ) := (g46_M_mono μ hμ0 hatom).measurable
  have hMb : IsLocallyBounded (renewalFn μ) := by
    intro T hT
    refine ⟨renewalFn μ T, fun t ht => ?_⟩
    have h0 : 0 ≤ renewalFn μ t := ENNReal.toReal_nonneg
    rw [abs_of_nonneg h0]
    exact g46_M_mono μ hμ0 hatom ht.2
  refine ⟨g46_rm_fin μ hμ0 hatom, heq, fun m hm hmb hmeq => ?_⟩
  exact g46_uniq_lin μ hμ0 hatom (cdf μ) m (renewalFn μ) hm hmb hMm hMb hmeq heq

theorem g46_re (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hint : Integrable id μ) (hmean : ∫ x, x ∂μ = 1) :
    (∀ t : ℝ, renewalMeasure μ (Set.Iic t) < ⊤) ∧
    (∀ t : ℝ, 0 ≤ t →
      renewalFn μ t = cdf μ t + ∫ u in Set.Icc 0 t, renewalFn μ (t - u) ∂μ) ∧
    (∀ m : ℝ → ℝ, Measurable m → IsLocallyBounded m →
      (∀ t : ℝ, 0 ≤ t → m t = cdf μ t + ∫ u in Set.Icc 0 t, m (t - u) ∂μ) →
      Set.EqOn m (renewalFn μ) (Set.Ici 0)) :=
  g46_re_core μ hμ0 (g46_atom_of_mean μ hmean)

lemma g46_tail_anti (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Antitone (ReedGGN.Regulator.tail μ) := by
  intro a b hab
  exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Ioi_subset_Ioi hab))

lemma g46_tail_bd (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    0 ≤ ReedGGN.Regulator.tail μ x ∧ ReedGGN.Regulator.tail μ x ≤ 1 :=
  ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal zero_le_one
    (by rw [ENNReal.ofReal_one]; exact prob_le_one)⟩

lemma g46_tail_intOn (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) :
    IntegrableOn (ReedGGN.Regulator.tail μ) (Set.Icc 0 x) := by
  refine Integrable.of_bound (g46_tail_anti μ).measurable.aestronglyMeasurable 1 ?_
  refine Eventually.of_forall (fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (g46_tail_bd μ u).1]; exact (g46_tail_bd μ u).2

lemma g46_Fe_mono (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Monotone (ReedGGN.Regulator.Fe μ) := by
  intro a b hab
  unfold ReedGGN.Regulator.Fe
  apply setIntegral_mono_set (g46_tail_intOn μ b)
  · exact Eventually.of_forall (fun u => (g46_tail_bd μ u).1)
  · exact Eventually.of_forall (Set.Icc_subset_Icc_right hab)

lemma g46_Fe_bd (μ : Measure ℝ) [IsProbabilityMeasure μ] (x : ℝ) (hx : 0 ≤ x) :
    |ReedGGN.Regulator.Fe μ x| ≤ x := by
  have := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Set.Icc (0:ℝ) x)
    (f := ReedGGN.Regulator.tail μ) (C := 1) (by simp)
    (fun u _ => by rw [Real.norm_eq_abs, abs_of_nonneg (g46_tail_bd μ u).1]; exact (g46_tail_bd μ u).2)
  simpa [Real.norm_eq_abs, Measure.real, Real.volume_Icc, hx, ReedGGN.Regulator.Fe] using this

lemma g46_Fe_meas (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Measurable (ReedGGN.Regulator.Fe μ) := (g46_Fe_mono μ).measurable

lemma g46_Fe_lb (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    IsLocallyBounded (ReedGGN.Regulator.Fe μ) := by
  intro T hT
  exact ⟨T, fun t ht => (g46_Fe_bd μ t ht.1).trans ht.2⟩

lemma g46_eq_id (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ0 : μ (Set.Iio 0) = 0)
    (t : ℝ) (ht : 0 ≤ t) :
    t = ReedGGN.Regulator.Fe μ t + ∫ u in Set.Icc 0 t, (t - u) ∂μ := by
  -- Fubini
  have hA : ∫ u in Set.Icc 0 t, (t - u) ∂μ = ∫ s in Set.Icc 0 t, (μ (Set.Icc 0 s)).toReal := by
    have hmS : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} := measurableSet_le measurable_fst measurable_snd
    have hint : Integrable (Function.uncurry fun u s : ℝ => ({p : ℝ × ℝ | p.1 ≤ p.2}).indicator
        (fun _ => (1:ℝ)) (u, s)) ((μ.restrict (Set.Icc 0 t)).prod (volume.restrict (Set.Icc 0 t))) := by
      refine Integrable.of_bound ?_ 1 ?_
      · exact (measurable_const.indicator hmS).aestronglyMeasurable
      · refine Eventually.of_forall (fun p => ?_)
        simp only [Function.uncurry]
        by_cases h : p ∈ {p : ℝ × ℝ | p.1 ≤ p.2}
        · rw [Set.indicator_of_mem h]; simp
        · rw [Set.indicator_of_notMem h]; simp
    have hsw := integral_integral_swap hint
    have l1 : ∀ u ∈ Set.Icc 0 t, ∫ s in Set.Icc 0 t, ({p : ℝ × ℝ | p.1 ≤ p.2}).indicator
        (fun _ => (1:ℝ)) (u, s) = t - u := by
      intro u hu
      have : (fun s => ({p : ℝ × ℝ | p.1 ≤ p.2}).indicator (fun _ => (1:ℝ)) (u, s))
          = (Set.Ici u).indicator (fun _ => (1:ℝ)) := by
        funext s; simp [Set.indicator]
      rw [this, integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
      have e : Set.Ici u ∩ Set.Icc 0 t = Set.Icc u t := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
        constructor
        · rintro ⟨h1, _, h3⟩; exact ⟨h1, h3⟩
        · rintro ⟨h1, h3⟩; exact ⟨h1, hu.1.trans h1, h3⟩
      rw [e]; simp [Measure.real, Real.volume_Icc, hu.2]
    have l2 : ∀ s ∈ Set.Icc 0 t, ∫ u in Set.Icc 0 t, ({p : ℝ × ℝ | p.1 ≤ p.2}).indicator
        (fun _ => (1:ℝ)) (u, s) ∂μ = (μ (Set.Icc 0 s)).toReal := by
      intro s hs
      have : (fun u => ({p : ℝ × ℝ | p.1 ≤ p.2}).indicator (fun _ => (1:ℝ)) (u, s))
          = (Set.Iic s).indicator (fun _ => (1:ℝ)) := by
        funext u; simp [Set.indicator]
      rw [this, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
      have e : Set.Iic s ∩ Set.Icc 0 t = Set.Icc 0 s := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
        constructor
        · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
        · rintro ⟨h1, h3⟩; exact ⟨h3, h1, h3.trans hs.2⟩
      rw [e]; simp [Measure.real]
    rw [setIntegral_congr_fun measurableSet_Icc (fun u hu => (l1 u hu).symm), hsw,
      setIntegral_congr_fun measurableSet_Icc l2]
  have hB : ∀ s ∈ Set.Icc 0 t, (μ (Set.Icc 0 s)).toReal + ReedGGN.Regulator.tail μ s = 1 := by
    intro s hs
    unfold ReedGGN.Regulator.tail
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), ← g46_Iic_eq_Icc _ hμ0,
      ← measure_union ?_ measurableSet_Ioi, Set.Iic_union_Ioi, measure_univ, ENNReal.toReal_one]
    exact Set.disjoint_left.mpr fun x h1 h2 => by simp at h1 h2; linarith
  have hmI : IntegrableOn (fun s => (μ (Set.Icc 0 s)).toReal) (Set.Icc 0 t) := by
    have hmono : Monotone fun s => (μ (Set.Icc 0 s)).toReal := fun a b hab =>
      ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Icc_subset_Icc_right hab))
    refine Integrable.of_bound hmono.measurable.aestronglyMeasurable 1 ?_
    refine Eventually.of_forall (fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
  rw [hA, ReedGGN.Regulator.Fe, add_comm, ← integral_add hmI (g46_tail_intOn μ t),
    setIntegral_congr_fun measurableSet_Icc hB]
  simp [Measure.real, Real.volume_Icc, ht]

theorem g46_eqid (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hint : Integrable id μ) (hmean : ∫ x, x ∂μ = 1) :
    ∀ t : ℝ, 0 ≤ t →
      ReedGGN.Regulator.Fe μ t + ∫ s in Set.Icc 0 t, ReedGGN.Regulator.Fe μ (t - s) ∂(renewalMeasure μ) = t := by
  have hatom := g46_atom_of_mean μ hmean
  have h := g46_rte μ hμ0 hatom (ReedGGN.Regulator.Fe μ) (g46_Fe_meas μ) (g46_Fe_lb μ)
  intro t ht
  have := h.2.2 (fun s => s) measurable_id (fun T hT => ⟨T, fun s hs => by
    rw [abs_of_nonneg hs.1]; exact hs.2⟩) (fun s hs => g46_eq_id μ hμ0 s hs) (Set.mem_Ici.mpr ht)
  exact this.symm

lemma g46_exp_cdf (x : ℝ) (hx : 0 ≤ x) : (expMeasure 1 (Set.Iic x)).toReal = 1 - Real.exp (-x) := by
  haveI := isProbabilityMeasure_expMeasure (r := 1) one_pos
  have := cdf_expMeasure_eq (r := 1) one_pos x
  rw [cdf_eq_real, if_pos hx, one_mul] at this
  simpa [Measure.real] using this

lemma g46_exp_Iic0 : expMeasure 1 (Set.Iic 0) = 0 := by
  have h := g46_exp_cdf 0 le_rfl
  simp only [neg_zero, Real.exp_zero, sub_self] at h
  rw [ENNReal.toReal_eq_zero_iff] at h
  rcases h with h | h
  · exact h
  · haveI := isProbabilityMeasure_expMeasure (r := 1) one_pos
    exact absurd h (measure_ne_top _ _)

theorem g46_exp :
    (∀ t : ℝ, 0 ≤ t → renewalMeasure (expMeasure 1) (Set.Iic t) = ENNReal.ofReal t) ∧
    (∀ (ζ : ℝ → ℝ) (β : ℝ) (q : ℝ → ℝ), ReedGGN.Regulator.IsCadlag ζ → ReedGGN.Regulator.IsCadlag q →
      (SolvesRenewalEq (expMeasure 1) ζ β q ↔
        ∀ t : ℝ, 0 ≤ t →
          q t = ζ t + (∫ s in Set.Icc 0 t, ζ s) - β * t - ∫ s in Set.Icc 0 t, min (q s) 0)) := by
  haveI hp := isProbabilityMeasure_expMeasure (r := 1) one_pos
  set μ := expMeasure 1 with hμ
  have hμ0 : μ (Set.Iio 0) = 0 := measure_mono_null Set.Iio_subset_Iic_self g46_exp_Iic0
  have hatom : μ {0} < 1 := by
    have : μ {0} = 0 := measure_mono_null (by intro x hx; simp at hx; simp [hx]) g46_exp_Iic0
    rw [this]; exact zero_lt_one
  -- tail
  have htail : ∀ u, 0 ≤ u → ReedGGN.Regulator.tail μ u = Real.exp (-u) := by
    intro u hu
    unfold ReedGGN.Regulator.tail
    rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic,
      ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one, g46_exp_cdf u hu]
    ring
  have hFe : ∀ t, 0 ≤ t → ReedGGN.Regulator.Fe μ t = 1 - Real.exp (-t) := by
    intro t ht
    unfold ReedGGN.Regulator.Fe
    rw [setIntegral_congr_fun measurableSet_Icc (fun u hu => htail u hu.1),
      integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht,
      intervalIntegral.integral_comp_neg (fun x => Real.exp x), integral_exp]
    simp
  have hsolM : ∀ t, 0 ≤ t → (fun s : ℝ => s) t
      = cdf μ t + ∫ u in Set.Icc 0 t, (fun s : ℝ => s) (t - u) ∂μ := by
    intro t ht
    have := g46_eq_id μ hμ0 t ht
    rw [hFe t ht] at this
    rw [cdf_eq_real]
    simp only [Measure.real]
    rw [g46_exp_cdf t ht]; exact this
  have hR := g46_re_core μ hμ0 hatom
  have hMt : ∀ t, 0 ≤ t → renewalFn μ t = t := by
    intro t ht
    have h := hR.2.2 (fun s => s) measurable_id (fun T hT => ⟨T, fun s hs => by
      rw [abs_of_nonneg hs.1]; exact hs.2⟩) hsolM (Set.mem_Ici.mpr ht)
    exact h.symm
  have hA : ∀ t, 0 ≤ t → renewalMeasure μ (Set.Iic t) = ENNReal.ofReal t := by
    intro t ht
    have := hMt t ht
    rw [renewalFn] at this
    conv_rhs => rw [← this]
    rw [ENNReal.ofReal_toReal (hR.1 t).ne]
  refine ⟨hA, ?_⟩
  -- measure equality on [0,t]
  have hres : ∀ t, 0 ≤ t → (renewalMeasure μ).restrict (Set.Icc 0 t) = volume.restrict (Set.Icc 0 t) := by
    intro t ht
    haveI : IsFiniteMeasure ((renewalMeasure μ).restrict (Set.Icc 0 t)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact g46_rm_fin_Icc μ hμ0 hatom t⟩
    apply Measure.ext_of_Iic
    intro a
    rw [Measure.restrict_apply measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
    by_cases ha : a < 0
    · have : Set.Iic a ∩ Set.Icc 0 t = ∅ := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, Set.mem_empty_iff_false,
          iff_false, not_and]
        intro h1 h2; linarith
      rw [this, measure_empty, measure_empty]
    · push_neg at ha
      have : Set.Iic a ∩ Set.Icc 0 t = Set.Icc 0 (min a t) := by
        ext x; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc, le_min_iff]
        tauto
      rw [this, ← g46_Iic_eq_Icc _ (g46_rm_carried μ hμ0), hA _ (le_min ha ht), Real.volume_Icc,
        sub_zero]
  have hcv : ∀ t, 0 ≤ t → ∀ f : ℝ → ℝ,
      ∫ u in Set.Icc 0 t, f (t - u) ∂(renewalMeasure μ) = ∫ s in Set.Icc 0 t, f s := by
    intro t ht f
    rw [hres t ht, ← integral_indicator measurableSet_Icc]
    have e : (Set.Icc 0 t).indicator (fun u => f (t - u))
        = fun u => (Set.Icc 0 t).indicator f (t - u) := by
      funext u
      by_cases hu : u ∈ Set.Icc 0 t
      · rw [Set.indicator_of_mem hu, Set.indicator_of_mem (show t - u ∈ Set.Icc 0 t from
          ⟨by linarith [hu.2], by linarith [hu.1]⟩)]
      · rw [Set.indicator_of_notMem hu, Set.indicator_of_notMem (show t - u ∉ Set.Icc 0 t from
          fun h => hu ⟨by linarith [h.2], by linarith [h.1]⟩)]
    rw [e, integral_sub_left_eq_self ((Set.Icc 0 t).indicator f) volume t,
      integral_indicator measurableSet_Icc]
  intro ζ β q _ _
  unfold SolvesRenewalEq
  apply forall_congr'; intro t; apply imp_congr_right; intro ht
  have h1 := hcv t ht ζ
  have h2 := hcv t ht (fun s => min (q s) 0)
  rw [h1, h2]

end ReedGGN.RenewalRep

open ReedGGN.RenewalRep


theorem solution :
    (∀ t : ℝ, 0 ≤ t → renewalMeasure (expMeasure 1) (Set.Iic t) = ENNReal.ofReal t) ∧
    (∀ (ζ : ℝ → ℝ) (β : ℝ) (q : ℝ → ℝ), ReedGGN.Regulator.IsCadlag ζ → ReedGGN.Regulator.IsCadlag q →
      (SolvesRenewalEq (expMeasure 1) ζ β q ↔
        ∀ t : ℝ, 0 ≤ t →
          q t = ζ t + (∫ s in Set.Icc 0 t, ζ s) - β * t - ∫ s in Set.Icc 0 t, min (q s) 0)) := by
  exact g46_exp
