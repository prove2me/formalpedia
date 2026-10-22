-- Prove2me | solution 1 for ReedGGN.RenewalRep.corollary_5_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-22T05:28:56.059442+00:00
-- url     : https://prove2.me/submissions/72d6d6e8-3775-451e-8a46-d3ab506ffd73

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

lemma g46_rc_meas (g : ℝ → ℝ) (hg : ∀ t, ContinuousWithinAt g (Set.Ici t) t) : Measurable g := by
  let a : ℕ → ℝ → ℝ := fun n t => (((⌈t * (2:ℝ) ^ n⌉ : ℤ) : ℝ) / (2:ℝ) ^ n)
  have hmeas : ∀ n : ℕ, Measurable (fun t => g (a n t)) := by
    intro n
    show Measurable ((fun k : ℤ => g ((k : ℝ) / (2:ℝ) ^ n)) ∘ (fun t : ℝ => ⌈t * (2:ℝ) ^ n⌉))
    exact (measurable_of_countable _).comp (Int.measurable_ceil.comp (measurable_id.mul_const _))
  apply measurable_of_tendsto_metrizable hmeas
  rw [tendsto_pi_nhds]; intro t
  have h1 : ∀ n : ℕ, t ≤ a n t := fun n => by
    simp only [a]
    rw [le_div_iff₀ (by positivity)]; exact Int.le_ceil _
  have h2 : ∀ n : ℕ, a n t ≤ t + (1 / 2) ^ n := fun n => by
    simp only [a]
    rw [div_le_iff₀ (by positivity)]
    have := Int.ceil_lt_add_one (t * (2:ℝ) ^ n)
    have e : (t + (1 / 2) ^ n) * (2:ℝ) ^ n = t * 2 ^ n + 1 := by
      rw [add_mul, ← mul_pow]; norm_num
    rw [e]; linarith
  have hlim : Tendsto (fun n : ℕ => a n t) atTop (𝓝[≥] t) := by
    apply tendsto_nhdsWithin_iff.mpr; constructor
    · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _ h1 h2
      have : Tendsto (fun n : ℕ => ((1:ℝ) / 2) ^ n) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      simpa using tendsto_const_nhds.add this
    · exact Eventually.of_forall h1
  exact (hg t).tendsto.comp hlim

lemma g46_cad_rc (q : ℝ → ℝ) (hq : ReedGGN.Regulator.IsCadlag q) :
    ∀ t, ContinuousWithinAt (fun s => q (max s 0)) (Set.Ici t) t := by
  intro t
  by_cases ht : 0 ≤ t
  · have h := hq.1 t ht
    exact h.congr (fun s hs => by simp [max_eq_left (ht.trans hs)]) (by simp [max_eq_left ht])
  · push_neg at ht
    have : ∀ᶠ s in 𝓝 t, (fun s => q (max s 0)) s = q 0 := by
      filter_upwards [Iio_mem_nhds ht] with s hs; simp [max_eq_right (le_of_lt (Set.mem_Iio.mp hs))]
    exact (continuousAt_const.congr (this.mono fun s hs => hs.symm)).continuousWithinAt

lemma g46_cad_lb (q : ℝ → ℝ) (hq : ReedGGN.Regulator.IsCadlag q) : IsLocallyBounded q := by
  intro T hT
  refine (isCompact_Icc).induction_on (p := fun S => ∃ C, ∀ t ∈ S, |q t| ≤ C) ⟨0, by simp⟩ ?_ ?_ ?_
  · intro s t hst ⟨C, hC⟩; exact ⟨C, fun x hx => hC x (hst hx)⟩
  · intro s t ⟨C1, h1⟩ ⟨C2, h2⟩
    exact ⟨max C1 C2, fun x hx => hx.elim (fun h => (h1 x h).trans (le_max_left _ _))
      (fun h => (h2 x h).trans (le_max_right _ _))⟩
  · intro x hx
    have hA : q ⁻¹' Metric.ball (q x) 1 ∈ 𝓝[≥] x :=
      (hq.1 x hx.1).tendsto (Metric.ball_mem_nhds _ one_pos)
    have bA : ∀ y ∈ q ⁻¹' Metric.ball (q x) 1, |q y| ≤ |q x| + 1 := by
      intro y hy
      simp only [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hy
      have := abs_sub_abs_le_abs_sub (q y) (q x); linarith
    rcases eq_or_lt_of_le hx.1 with h0 | hpos
    · refine ⟨q ⁻¹' Metric.ball (q x) 1, ?_, ⟨_, bA⟩⟩
      rw [← h0] at hA ⊢
      exact nhdsWithin_mono _ Set.Icc_subset_Ici_self hA
    · obtain ⟨l, hl⟩ := hq.2 x hpos
      have hB : q ⁻¹' Metric.ball l 1 ∈ 𝓝[<] x := hl (Metric.ball_mem_nhds _ one_pos)
      have bB : ∀ y ∈ q ⁻¹' Metric.ball l 1, |q y| ≤ |l| + 1 := by
        intro y hy
        simp only [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hy
        have := abs_sub_abs_le_abs_sub (q y) l; linarith
      refine ⟨q ⁻¹' Metric.ball (q x) 1 ∪ q ⁻¹' Metric.ball l 1, ?_, ?_⟩
      · apply mem_nhdsWithin_of_mem_nhds
        rw [← nhdsLT_sup_nhdsGE x]
        exact ⟨mem_of_superset hB Set.subset_union_right, mem_of_superset hA Set.subset_union_left⟩
      · refine ⟨max (|q x| + 1) (|l| + 1), fun y hy => ?_⟩
        rcases hy with hy | hy
        · exact (bA y hy).trans (le_max_left _ _)
        · exact (bB y hy).trans (le_max_right _ _)

lemma g46_K_congr (ν : Measure ℝ) (f g : ℝ → ℝ) (h : ∀ s, 0 ≤ s → f s = g s) (t : ℝ) :
    ∫ u in Set.Icc 0 t, f (t - u) ∂ν = ∫ u in Set.Icc 0 t, g (t - u) ∂ν :=
  setIntegral_congr_fun measurableSet_Icc (fun u hu => h _ (by linarith [hu.2]))

lemma g46_intOn_lb (ν : Measure ℝ) {t : ℝ} (ht : 0 ≤ t) (hfin : ν (Set.Icc 0 t) < ⊤) {f : ℝ → ℝ}
    (hf : Measurable f) (hb : IsLocallyBounded f) :
    IntegrableOn (fun u => f (t - u)) (Set.Icc 0 t) ν := by
  obtain ⟨C, hC⟩ := hb t ht
  exact g46_intOn ν hfin hf hC

lemma g46_K_lb (ν : Measure ℝ) (hfin : ∀ s, ν (Set.Iic s) < ⊤) {f : ℝ → ℝ}
    (hb : IsLocallyBounded f) : IsLocallyBounded (fun s => ∫ u in Set.Icc 0 s, f (s - u) ∂ν) := by
  intro T hT
  obtain ⟨C, hC⟩ := hb T hT
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0 ⟨le_rfl, hT⟩)
  refine ⟨C * (ν (Set.Iic T)).toReal, fun t ht => ?_⟩
  have h1 := g46_K_bound ν ((measure_mono Set.Icc_subset_Iic_self).trans_lt (hfin t)) (f := f)
    (C := C) (fun s hs => hC s ⟨hs.1, hs.2.trans ht.2⟩)
  have h2 : (ν (Set.Icc 0 t)).toReal ≤ (ν (Set.Iic T)).toReal :=
    ENNReal.toReal_mono (hfin T).ne
      (measure_mono (Set.Icc_subset_Iic_self.trans (Set.Iic_subset_Iic.mpr ht.2)))
  exact h1.trans (mul_le_mul_of_nonneg_left h2 hC0)

lemma g46_min_lb (f : ℝ → ℝ) (hb : IsLocallyBounded f) : IsLocallyBounded (fun s => min (f s) 0) := by
  intro T hT; obtain ⟨C, hC⟩ := hb T hT
  refine ⟨C, fun s hs => ?_⟩
  have := hC s hs
  show |min (f s) 0| ≤ C
  rcases le_total (f s) 0 with h | h
  · rw [min_eq_left h]; exact this
  · rw [min_eq_right h, abs_zero]; exact (abs_nonneg _).trans this

lemma g46_Kdm_qm (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ0 : μ (Set.Iio 0) = 0)
    (hatom : μ {0} < 1) (g : ℝ → ℝ) (hgm : Measurable g) (hgb : IsLocallyBounded g) (t : ℝ) (ht : 0 ≤ t) :
    ∫ u in Set.Icc 0 t, g (t - u) ∂(renewalMeasure μ)
      = (∫ u in Set.Icc 0 t, g (t - u) ∂μ)
        + ∫ u in Set.Icc 0 t, (∫ v in Set.Icc 0 (t - u), g (t - u - v) ∂μ) ∂(renewalMeasure μ) := by
  obtain ⟨Kg, hKg⟩ : ∃ Kg : ℝ → ℝ, Kg = fun s => ∫ u in Set.Icc 0 s, g (s - u) ∂μ := ⟨_, rfl⟩
  have hKgm : Measurable Kg := hKg ▸ g46_K_meas μ hgm
  have hKgb : IsLocallyBounded Kg := hKg ▸ g46_K_lb μ (fun s => measure_lt_top _ _) hgb
  have hR2 := g46_rte μ hμ0 hatom Kg hKgm hKgb
  have hr1m := g46_K_meas (renewalMeasure μ) hgm
  have hr1b := g46_K_lb (renewalMeasure μ) (g46_rm_fin μ hμ0 hatom) hgb
  have hr1eq : ∀ s, 0 ≤ s → (fun s => ∫ u in Set.Icc 0 s, g (s - u) ∂(renewalMeasure μ)) s
      = Kg s + ∫ u in Set.Icc 0 s, (fun s => ∫ u in Set.Icc 0 s, g (s - u) ∂(renewalMeasure μ)) (s - u) ∂μ := by
    intro s hs
    obtain ⟨C, hC⟩ := hgb s hs
    rw [hKg]
    exact g46_KdM_split μ hμ0 hatom hgm hC
  have := hR2.2.2 _ hr1m hr1b hr1eq (Set.mem_Ici.mpr ht)
  simp only at this
  rw [this, hKg]

theorem g46_core (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hatom : μ {0} < 1)
    (ζ : ℝ → ℝ) (hζ : ReedGGN.Regulator.IsCadlag ζ) (β : ℝ) (q : ℝ → ℝ)
    (hq : ReedGGN.Regulator.IsCadlag q) :
    ∃ qt H : ℝ → ℝ, Measurable qt ∧ IsLocallyBounded qt ∧ (∀ s, 0 ≤ s → qt s = q s) ∧
      Measurable H ∧ IsLocallyBounded H ∧
      (∀ t, 0 ≤ t → H t + ∫ u in Set.Icc 0 t, H (t - u) ∂(renewalMeasure μ) =
        ζ t + (∫ u in Set.Icc 0 t, ζ (t - u) ∂(renewalMeasure μ))
        - β * (ReedGGN.Regulator.Fe μ t + ∫ s in Set.Icc 0 t, ReedGGN.Regulator.Fe μ (t - s) ∂(renewalMeasure μ))
        - ∫ u in Set.Icc 0 t, min (q (t - u)) 0 ∂(renewalMeasure μ)) ∧
      (∀ t, 0 ≤ t → ((q t = ζ t - β * ReedGGN.Regulator.Fe μ t + ∫ s in Set.Icc 0 t, max (q (t - s)) 0 ∂μ) ↔
        qt t = H t + ∫ u in Set.Icc 0 t, qt (t - u) ∂μ)) := by
  have hfinM := g46_rm_fin μ hμ0 hatom
  have hfinM' := g46_rm_fin_Icc μ hμ0 hatom
  have hfinμ : ∀ s, μ (Set.Iic s) < ⊤ := fun s => measure_lt_top _ _
  obtain ⟨qt, hqt⟩ : ∃ qt : ℝ → ℝ, qt = fun s => q (max s 0) := ⟨_, rfl⟩
  obtain ⟨zt, hzt⟩ : ∃ zt : ℝ → ℝ, zt = fun s => ζ (max s 0) := ⟨_, rfl⟩
  have hqtm : Measurable qt := hqt ▸ g46_rc_meas _ (g46_cad_rc q hq)
  have hztm : Measurable zt := hzt ▸ g46_rc_meas _ (g46_cad_rc ζ hζ)
  have hqeq : ∀ s, 0 ≤ s → qt s = q s := fun s hs => by simp [hqt, max_eq_left hs]
  have hzeq : ∀ s, 0 ≤ s → zt s = ζ s := fun s hs => by simp [hzt, max_eq_left hs]
  have hqtb : IsLocallyBounded qt := by
    intro T hT; obtain ⟨C, hC⟩ := g46_cad_lb q hq T hT
    exact ⟨C, fun s hs => by rw [hqeq s hs.1]; exact hC s hs⟩
  have hztb : IsLocallyBounded zt := by
    intro T hT; obtain ⟨C, hC⟩ := g46_cad_lb ζ hζ T hT
    exact ⟨C, fun s hs => by rw [hzeq s hs.1]; exact hC s hs⟩
  obtain ⟨qm, hqm⟩ : ∃ qm : ℝ → ℝ, qm = fun s => min (qt s) 0 := ⟨_, rfl⟩
  have hqmm : Measurable qm := hqm ▸ hqtm.min measurable_const
  have hqmb : IsLocallyBounded qm := hqm ▸ g46_min_lb qt hqtb
  obtain ⟨Kqm, hKqm⟩ : ∃ K : ℝ → ℝ, K = fun s => ∫ u in Set.Icc 0 s, qm (s - u) ∂μ := ⟨_, rfl⟩
  have hKqmm : Measurable Kqm := hKqm ▸ g46_K_meas μ hqmm
  have hKqmb : IsLocallyBounded Kqm := hKqm ▸ g46_K_lb μ hfinμ hqmb
  obtain ⟨H, hH⟩ : ∃ H : ℝ → ℝ, H = fun s => zt s - β * ReedGGN.Regulator.Fe μ s - Kqm s := ⟨_, rfl⟩
  have hHm : Measurable H := hH ▸ (hztm.sub (measurable_const.mul (g46_Fe_meas μ))).sub hKqmm
  have hHb : IsLocallyBounded H := by
    intro T hT
    obtain ⟨C1, h1⟩ := hztb T hT; obtain ⟨C3, h3⟩ := hKqmb T hT
    refine ⟨C1 + |β| * T + C3, fun s hs => ?_⟩
    have h2 : |β * ReedGGN.Regulator.Fe μ s| ≤ |β| * T := by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left ((g46_Fe_bd μ s hs.1).trans hs.2) (abs_nonneg _)
    rw [hH]
    calc |zt s - β * ReedGGN.Regulator.Fe μ s - Kqm s|
        ≤ |zt s| + |β * ReedGGN.Regulator.Fe μ s| + |Kqm s| :=
          (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ C1 + |β| * T + C3 := by linarith [h1 s hs, h3 s hs]
  refine ⟨qt, H, hqtm, hqtb, hqeq, hHm, hHb, ?_, ?_⟩
  · intro t ht
    have eH : ∫ u in Set.Icc 0 t, H (t - u) ∂(renewalMeasure μ)
        = ∫ u in Set.Icc 0 t, zt (t - u) ∂(renewalMeasure μ)
          - β * ∫ u in Set.Icc 0 t, ReedGGN.Regulator.Fe μ (t - u) ∂(renewalMeasure μ)
          - ∫ u in Set.Icc 0 t, Kqm (t - u) ∂(renewalMeasure μ) := by
      have i1 : IntegrableOn (fun u => zt (t - u)) (Set.Icc 0 t) (renewalMeasure μ) :=
        g46_intOn_lb _ ht (hfinM' t) hztm hztb
      have i2 : IntegrableOn (fun u => β * ReedGGN.Regulator.Fe μ (t - u)) (Set.Icc 0 t)
          (renewalMeasure μ) :=
        (g46_intOn_lb _ ht (hfinM' t) (g46_Fe_meas μ) (g46_Fe_lb μ)).const_mul β
      have i12 : IntegrableOn (fun u => zt (t - u) - β * ReedGGN.Regulator.Fe μ (t - u))
          (Set.Icc 0 t) (renewalMeasure μ) := i1.sub i2
      have i3 : IntegrableOn (fun u => Kqm (t - u)) (Set.Icc 0 t) (renewalMeasure μ) :=
        g46_intOn_lb _ ht (hfinM' t) hKqmm hKqmb
      rw [hH]; beta_reduce
      rw [integral_sub i12 i3, integral_sub i1 i2, integral_const_mul]
    have eZ := g46_K_congr (renewalMeasure μ) zt ζ hzeq t
    have eQ := g46_Kdm_qm μ hμ0 hatom qm hqmm hqmb t ht
    have eQ2 : ∫ u in Set.Icc 0 t, qm (t - u) ∂(renewalMeasure μ)
        = ∫ u in Set.Icc 0 t, min (q (t - u)) 0 ∂(renewalMeasure μ) :=
      g46_K_congr (renewalMeasure μ) qm (fun s => min (q s) 0)
        (fun s hs => by simp only [hqm]; rw [hqeq s hs]) t
    have eKt : Kqm t = ∫ u in Set.Icc 0 t, qm (t - u) ∂μ := by rw [hKqm]
    have eK2 : ∫ u in Set.Icc 0 t, Kqm (t - u) ∂(renewalMeasure μ)
        = ∫ u in Set.Icc 0 t, (∫ v in Set.Icc 0 (t - u), qm (t - u - v) ∂μ) ∂(renewalMeasure μ) := by
      rw [hKqm]
    have eHt : H t = ζ t - β * ReedGGN.Regulator.Fe μ t - Kqm t := by rw [hH]; simp only [hzeq t ht]
    rw [eH, eHt, eZ, eK2, ← eQ2]
    linarith [eQ, eKt]
  · intro t ht
    have e1 : ∫ s in Set.Icc 0 t, max (q (t - s)) 0 ∂μ
        = ∫ s in Set.Icc 0 t, (qt (t - s) - qm (t - s)) ∂μ := by
      apply setIntegral_congr_fun measurableSet_Icc; intro s hs
      simp only [hqm]; rw [hqeq _ (by linarith [hs.2])]
      rcases le_total (q (t - s)) 0 with h | h
      · rw [max_eq_right h, min_eq_left h]; ring
      · rw [max_eq_left h, min_eq_right h]; ring
    rw [e1, integral_sub (g46_intOn_lb μ ht (measure_lt_top _ _) hqtm hqtb)
      (g46_intOn_lb μ ht (measure_lt_top _ _) hqmm hqmb)]
    have eKt : Kqm t = ∫ u in Set.Icc 0 t, qm (t - u) ∂μ := by rw [hKqm]
    have eHt : H t = ζ t - β * ReedGGN.Regulator.Fe μ t - Kqm t := by rw [hH]; simp only [hzeq t ht]
    rw [hqeq t ht, eHt, eKt]
    constructor <;> intro h <;> linarith

theorem g46_544' (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hint : Integrable id μ) (hmean : ∫ x, x ∂μ = 1)
    (ζ : ℝ → ℝ) (hζ : ReedGGN.Regulator.IsCadlag ζ) (β : ℝ) (q : ℝ → ℝ) (hq : ReedGGN.Regulator.IsCadlag q)
    (hsol : SolvesLimitEq μ ζ β q) :
    ∀ t : ℝ, 0 ≤ t →
      q t = ζ t + (∫ u in Set.Icc 0 t, ζ (t - u) ∂(renewalMeasure μ))
        - β * (ReedGGN.Regulator.Fe μ t + ∫ s in Set.Icc 0 t, ReedGGN.Regulator.Fe μ (t - s) ∂(renewalMeasure μ))
        - ∫ u in Set.Icc 0 t, min (q (t - u)) 0 ∂(renewalMeasure μ) := by
  have hatom := g46_atom_of_mean μ hmean
  obtain ⟨qt, H, hqtm, hqtb, hqeq, hHm, hHb, hb, hc⟩ := g46_core μ hμ0 hatom ζ hζ β q hq
  have hR := g46_rte μ hμ0 hatom H hHm hHb
  intro t ht
  have hrep := hR.2.2 qt hqtm hqtb (fun t ht => (hc t ht).mp (hsol t ht)) (Set.mem_Ici.mpr ht)
  simp only at hrep
  rw [← hqeq t ht, hrep, hb t ht]

theorem g46_equiv (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hint : Integrable id μ) (hmean : ∫ x, x ∂μ = 1)
    (ζ : ℝ → ℝ) (hζ : ReedGGN.Regulator.IsCadlag ζ) (β : ℝ) :
    ∀ q : ℝ → ℝ, ReedGGN.Regulator.IsCadlag q → (SolvesLimitEq μ ζ β q ↔ SolvesRenewalEq μ ζ β q) := by
  have hatom := g46_atom_of_mean μ hmean
  intro q hq
  obtain ⟨qt, H, hqtm, hqtb, hqeq, hHm, hHb, hb, hc⟩ := g46_core μ hμ0 hatom ζ hζ β q hq
  have hR := g46_rte μ hμ0 hatom H hHm hHb
  have hE := g46_eqid μ hμ0 hint hmean
  constructor
  · intro hsol t ht
    have hrep := hR.2.2 qt hqtm hqtb (fun t ht => (hc t ht).mp (hsol t ht)) (Set.mem_Ici.mpr ht)
    simp only at hrep
    rw [← hqeq t ht, hrep, hb t ht, hE t ht]
  · intro hren t ht
    have hqr : ∀ s, 0 ≤ s → qt s = H s + ∫ u in Set.Icc 0 s, H (s - u) ∂(renewalMeasure μ) := by
      intro s hs; rw [hqeq s hs, hb s hs, hE s hs]; exact hren s hs
    apply (hc t ht).mpr
    have h2 := hR.2.1 t ht
    simp only at h2
    rw [hqr t ht]
    refine h2.trans ?_
    congr 1
    exact setIntegral_congr_fun measurableSet_Icc (fun u hu => (hqr (t - u) (by linarith [hu.2])).symm)

lemma g46_max_lb (f : ℝ → ℝ) (hb : IsLocallyBounded f) : IsLocallyBounded (fun s => max (f s) 0) := by
  intro T hT; obtain ⟨C, hC⟩ := hb T hT
  refine ⟨C, fun s hs => ?_⟩
  have := hC s hs
  show |max (f s) 0| ≤ C
  rcases le_total (f s) 0 with h | h
  · rw [max_eq_right h, abs_zero]; exact (abs_nonneg _).trans this
  · rw [max_eq_left h]; exact this

lemma g46_lim_uniq (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ0 : μ (Set.Iio 0) = 0)
    (hatom : μ {0} < 1) (ζ : ℝ → ℝ) (hζ : ReedGGN.Regulator.IsCadlag ζ) (β : ℝ)
    (q1 q2 : ℝ → ℝ) (hq1 : ReedGGN.Regulator.IsCadlag q1) (hq2 : ReedGGN.Regulator.IsCadlag q2)
    (h1 : SolvesLimitEq μ ζ β q1) (h2 : SolvesLimitEq μ ζ β q2) : Set.EqOn q1 q2 (Set.Ici 0) := by
  obtain ⟨a, -, ham, hab, haeq, -⟩ := g46_core μ hμ0 hatom ζ hζ β q1 hq1
  obtain ⟨b, -, hbm, hbb, hbeq, -⟩ := g46_core μ hμ0 hatom ζ hζ β q2 hq2
  have key := g46_uniq μ hμ0 hatom (fun s => a s - b s) (ham.sub hbm) ?_ ?_
  · intro t ht
    have := key t ht
    rw [haeq t ht, hbeq t ht] at this; linarith
  · intro T hT; obtain ⟨C1, hC1⟩ := hab T hT; obtain ⟨C2, hC2⟩ := hbb T hT
    exact ⟨C1 + C2, fun s hs => (abs_sub _ _).trans (add_le_add (hC1 s hs) (hC2 s hs))⟩
  · intro t ht
    have i1 := g46_intOn_lb μ ht (measure_lt_top _ _) (ham.max measurable_const) (g46_max_lb a hab)
    have i2 := g46_intOn_lb μ ht (measure_lt_top _ _) (hbm.max measurable_const) (g46_max_lb b hbb)
    have i3 := g46_intOn_lb μ ht (measure_lt_top _ _) (ham.sub hbm)
      (show IsLocallyBounded (fun s => a s - b s) from by
        intro T hT; obtain ⟨C1, hC1⟩ := hab T hT; obtain ⟨C2, hC2⟩ := hbb T hT
        exact ⟨C1 + C2, fun s hs => (abs_sub _ _).trans (add_le_add (hC1 s hs) (hC2 s hs))⟩)
    have ea := g46_K_congr μ (fun s => max (q1 s) 0) (fun s => max (a s) 0)
      (fun s hs => by rw [haeq s hs]) t
    have eb := g46_K_congr μ (fun s => max (q2 s) 0) (fun s => max (b s) 0)
      (fun s hs => by rw [hbeq s hs]) t
    have e : a t - b t = ∫ s in Set.Icc 0 t, (max (a (t - s)) 0 - max (b (t - s)) 0) ∂μ := by
      rw [integral_sub i1 i2, haeq t ht, hbeq t ht, h1 t ht, h2 t ht, ea, eb]; ring
    rw [e]
    refine abs_integral_le_integral_abs.trans ?_
    apply setIntegral_mono_on (i1.sub i2).abs i3.abs measurableSet_Icc
    intro s _
    exact abs_max_sub_max_le_abs _ _ _

lemma g46_shift_ge (t u : ℝ) : Tendsto (fun s => s - u) (𝓝[≥] t) (𝓝[≥] (t - u)) :=
  tendsto_nhdsWithin_iff.mpr ⟨((continuous_sub_right u).tendsto t).mono_left nhdsWithin_le_nhds,
    eventually_nhdsWithin_of_forall (fun s hs => by simp only [Set.mem_Ici] at hs ⊢; linarith)⟩

lemma g46_shift_lt (t u : ℝ) : Tendsto (fun s => s - u) (𝓝[<] t) (𝓝[<] (t - u)) :=
  tendsto_nhdsWithin_iff.mpr ⟨((continuous_sub_right u).tendsto t).mono_left nhdsWithin_le_nhds,
    eventually_nhdsWithin_of_forall (fun s hs => by simp only [Set.mem_Iio] at hs ⊢; linarith)⟩

lemma g46_K_cadlag (μ : Measure ℝ) [IsFiniteMeasure μ] (g : ℝ → ℝ) (hgm : Measurable g)
    (hg : ReedGGN.Regulator.IsCadlag g) :
    ReedGGN.Regulator.IsCadlag (fun s => ∫ u in Set.Icc 0 s, g (s - u) ∂μ) := by
  have hlb := g46_cad_lb g hg
  have hK : ∀ s, ∫ u in Set.Icc 0 s, g (s - u) ∂μ
      = ∫ u, (Set.Icc 0 s).indicator (fun u => g (s - u)) u ∂μ :=
    fun s => (integral_indicator measurableSet_Icc).symm
  have hFm : ∀ s, AEStronglyMeasurable ((Set.Icc 0 s).indicator (fun u => g (s - u))) μ :=
    fun s => ((hgm.comp (measurable_const.sub measurable_id)).indicator
      measurableSet_Icc).aestronglyMeasurable
  constructor
  · intro t ht
    obtain ⟨C, hC⟩ := hlb (t + 1) (by linarith)
    have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0 ⟨le_rfl, by linarith⟩)
    unfold ContinuousWithinAt
    simp_rw [hK]
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => C)
    · exact Eventually.of_forall hFm
    · filter_upwards [Ico_mem_nhdsGE (show t < t + 1 by linarith)] with s hs
      refine Eventually.of_forall (fun u => ?_)
      by_cases hu : u ∈ Set.Icc 0 s
      · rw [Set.indicator_of_mem hu, Real.norm_eq_abs]
        exact hC _ ⟨by linarith [hu.2], by linarith [hu.1, hs.2]⟩
      · rw [Set.indicator_of_notMem hu, norm_zero]; exact hC0
    · exact integrable_const C
    · refine Eventually.of_forall (fun u => ?_)
      rcases lt_or_ge u 0 with hu0 | hu0
      · have : ∀ s, (Set.Icc 0 s).indicator (fun u => g (s - u)) u = 0 := fun s =>
          Set.indicator_of_notMem (fun h => by linarith [h.1]) _
        simp only [this]; exact tendsto_const_nhds
      rcases le_or_gt u t with hut | hut
      · rw [Set.indicator_of_mem (show u ∈ Set.Icc 0 t from ⟨hu0, hut⟩)]
        have hev : (fun s => g (s - u)) =ᶠ[𝓝[≥] t]
            (fun s => (Set.Icc 0 s).indicator (fun u => g (s - u)) u) := by
          filter_upwards [self_mem_nhdsWithin] with s hs
          rw [Set.indicator_of_mem (show u ∈ Set.Icc 0 s from ⟨hu0, hut.trans hs⟩)]
        exact (((hg.1 (t - u) (by linarith)).tendsto).comp (g46_shift_ge t u)).congr' hev
      · rw [Set.indicator_of_notMem (show u ∉ Set.Icc 0 t from fun h => by linarith [h.2])]
        have hev : (fun _ => (0:ℝ)) =ᶠ[𝓝[≥] t]
            (fun s => (Set.Icc 0 s).indicator (fun u => g (s - u)) u) := by
          filter_upwards [Ico_mem_nhdsGE hut] with s hs
          rw [Set.indicator_of_notMem (show u ∉ Set.Icc 0 s from fun h => by linarith [h.2, hs.2])]
        exact tendsto_const_nhds.congr' hev
  · intro t ht
    let gl : ℝ → ℝ := fun v => if h : 0 < v then Classical.choose (hg.2 v h) else 0
    have hgl : ∀ v, 0 < v → Tendsto g (𝓝[<] v) (𝓝 (gl v)) := fun v hv => by
      simp only [gl, dif_pos hv]; exact Classical.choose_spec (hg.2 v hv)
    obtain ⟨C, hC⟩ := hlb t ht.le
    have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0 ⟨le_rfl, ht.le⟩)
    refine ⟨∫ u, (Set.Ico 0 t).indicator (fun u => gl (t - u)) u ∂μ, ?_⟩
    simp_rw [hK]
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => C)
    · exact Eventually.of_forall hFm
    · filter_upwards [self_mem_nhdsWithin] with s hs
      refine Eventually.of_forall (fun u => ?_)
      by_cases hu : u ∈ Set.Icc 0 s
      · rw [Set.indicator_of_mem hu, Real.norm_eq_abs]
        exact hC _ ⟨by linarith [hu.2], by linarith [hu.1, (Set.mem_Iio.mp hs)]⟩
      · rw [Set.indicator_of_notMem hu, norm_zero]; exact hC0
    · exact integrable_const C
    · refine Eventually.of_forall (fun u => ?_)
      rcases lt_or_ge u 0 with hu0 | hu0
      · have : ∀ s, (Set.Icc 0 s).indicator (fun u => g (s - u)) u = 0 := fun s =>
          Set.indicator_of_notMem (fun h => by linarith [h.1]) _
        simp only [this]
        rw [Set.indicator_of_notMem (show u ∉ Set.Ico 0 t from fun h => by linarith [h.1])]
        exact tendsto_const_nhds
      rcases lt_or_ge u t with hut | hut
      · rw [Set.indicator_of_mem (show u ∈ Set.Ico 0 t from ⟨hu0, hut⟩)]
        have hev : (fun s => g (s - u)) =ᶠ[𝓝[<] t]
            (fun s => (Set.Icc 0 s).indicator (fun u => g (s - u)) u) := by
          filter_upwards [Ioo_mem_nhdsLT hut] with s hs
          rw [Set.indicator_of_mem (show u ∈ Set.Icc 0 s from ⟨hu0, hs.1.le⟩)]
        exact ((hgl (t - u) (by linarith)).comp (g46_shift_lt t u)).congr' hev
      · rw [Set.indicator_of_notMem (show u ∉ Set.Ico 0 t from fun h => by linarith [h.2])]
        have hev : (fun _ => (0:ℝ)) =ᶠ[𝓝[<] t]
            (fun s => (Set.Icc 0 s).indicator (fun u => g (s - u)) u) := by
          filter_upwards [self_mem_nhdsWithin] with s hs
          rw [Set.indicator_of_notMem (show u ∉ Set.Icc 0 s from
            fun h => by linarith [h.2, Set.mem_Iio.mp hs])]
        exact tendsto_const_nhds.congr' hev

lemma g46_cad_add {f g : ℝ → ℝ} (hf : ReedGGN.Regulator.IsCadlag f)
    (hg : ReedGGN.Regulator.IsCadlag g) : ReedGGN.Regulator.IsCadlag (fun s => f s + g s) :=
  ⟨fun t ht => (hf.1 t ht).add (hg.1 t ht), fun t ht => by
    obtain ⟨a, ha⟩ := hf.2 t ht; obtain ⟨b, hb⟩ := hg.2 t ht; exact ⟨a + b, ha.add hb⟩⟩

lemma g46_cad_sub {f g : ℝ → ℝ} (hf : ReedGGN.Regulator.IsCadlag f)
    (hg : ReedGGN.Regulator.IsCadlag g) : ReedGGN.Regulator.IsCadlag (fun s => f s - g s) :=
  ⟨fun t ht => (hf.1 t ht).sub (hg.1 t ht), fun t ht => by
    obtain ⟨a, ha⟩ := hf.2 t ht; obtain ⟨b, hb⟩ := hg.2 t ht; exact ⟨a - b, ha.sub hb⟩⟩

lemma g46_cad_const_mul {f : ℝ → ℝ} (c : ℝ) (hf : ReedGGN.Regulator.IsCadlag f) :
    ReedGGN.Regulator.IsCadlag (fun s => c * f s) :=
  ⟨fun t ht => continuousWithinAt_const.mul (hf.1 t ht), fun t ht => by
    obtain ⟨a, ha⟩ := hf.2 t ht; exact ⟨c * a, ha.const_mul c⟩⟩

lemma g46_cad_max0 {f : ℝ → ℝ} (hf : ReedGGN.Regulator.IsCadlag f) :
    ReedGGN.Regulator.IsCadlag (fun s => max (f s) 0) :=
  ⟨fun t ht => (hf.1 t ht).max continuousWithinAt_const, fun t ht => by
    obtain ⟨a, ha⟩ := hf.2 t ht; exact ⟨max a 0, ha.max tendsto_const_nhds⟩⟩

lemma g46_cad_congr {f g : ℝ → ℝ} (hf : ReedGGN.Regulator.IsCadlag f)
    (h : ∀ s, 0 ≤ s → g s = f s) : ReedGGN.Regulator.IsCadlag g :=
  ⟨fun t ht => (hf.1 t ht).congr (fun y hy => h y (ht.trans hy)) (h t ht), fun t ht => by
    obtain ⟨a, ha⟩ := hf.2 t ht
    refine ⟨a, ha.congr' ?_⟩
    filter_upwards [Ioo_mem_nhdsLT ht] with s hs
    exact (h s hs.1.le).symm⟩

lemma g46_Fe_cadlag (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    ReedGGN.Regulator.IsCadlag (ReedGGN.Regulator.Fe μ) := by
  have hP : Continuous (fun b => ∫ x in (0:ℝ)..b, ReedGGN.Regulator.tail μ x) :=
    intervalIntegral.continuous_primitive (fun a b => (g46_tail_anti μ).intervalIntegrable) 0
  have heq : ∀ s, 0 ≤ s → ReedGGN.Regulator.Fe μ s
      = ∫ x in (0:ℝ)..s, ReedGGN.Regulator.tail μ x := by
    intro s hs
    rw [intervalIntegral.integral_of_le hs, ← integral_Icc_eq_integral_Ioc]; rfl
  exact g46_cad_congr ⟨fun t _ => hP.continuousWithinAt,
    fun t _ => ⟨_, hP.continuousAt.tendsto.mono_left nhdsWithin_le_nhds⟩⟩ heq

lemma g46_iter (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ0 : μ (Set.Iio 0) = 0)
    (e : ℕ → ℝ → ℝ) (hem : ∀ n, Measurable (e n)) (T C : ℝ)
    (h0 : ∀ t ∈ Set.Icc 0 T, |e 0 t| ≤ C)
    (hstep : ∀ n, ∀ t ∈ Set.Icc 0 T, |e (n + 1) t| ≤ ∫ u in Set.Icc 0 t, |e n (t - u)| ∂μ) :
    ∀ n, ∀ t ∈ Set.Icc 0 T, |e n t| ≤ C * (convPow μ n (Set.Iic t)).toReal := by
  intro n
  induction n with
  | zero =>
    intro t ht
    have : (convPow μ 0 (Set.Iic t)).toReal = 1 := by
      simp [convPow, ht.1]
    rw [this, mul_one]; exact h0 t ht
  | succ n ih =>
    intro t ht
    haveI := g46_convPow_prob μ n
    have hT : 0 ≤ T := ht.1.trans ht.2
    have hcv := g46_K_conv (convPow μ n) μ (g46_convPow_carried μ hμ0 n) hμ0
      (fun s => measure_lt_top _ _) (f := fun _ => (1:ℝ)) measurable_const (t := t) (C := 1)
      (fun s _ => by simp)
    simp only [integral_const, smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply_univ] at hcv
    have hanti : Antitone fun u => (convPow μ n (Set.Iic (t - u))).toReal := by
      intro a b hab
      apply ENNReal.toReal_mono (measure_ne_top _ _)
      apply measure_mono; intro x hx; simp only [Set.mem_Iic] at hx ⊢; linarith
    have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (h0 0 ⟨le_rfl, hT⟩)
    have hle1 : ∀ s, (convPow μ n (Set.Iic s)).toReal ≤ 1 := fun s =>
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
    calc |e (n + 1) t| ≤ ∫ u in Set.Icc 0 t, |e n (t - u)| ∂μ := hstep n t ht
      _ ≤ ∫ u in Set.Icc 0 t, C * (convPow μ n (Set.Iic (t - u))).toReal ∂μ := by
        apply setIntegral_mono_on
        · exact g46_intOn μ (measure_lt_top _ _) (f := fun s => |e n s|) (hem n).abs
            (C := C) (fun s hs => by
              rw [abs_abs]
              exact (ih s ⟨hs.1, hs.2.trans ht.2⟩).trans
                (by nlinarith [hle1 s, (ENNReal.toReal_nonneg : 0 ≤ (convPow μ n (Set.Iic s)).toReal)]))
        · refine Integrable.of_bound ((hanti.measurable.const_mul C).aestronglyMeasurable) C ?_
          refine Eventually.of_forall (fun u => ?_)
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC0 ENNReal.toReal_nonneg)]
          nlinarith [hle1 (t - u)]
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

lemma g46_unif_cadlag (X : ℕ → ℝ → ℝ) (x : ℝ → ℝ) (hX : ∀ n, ReedGGN.Regulator.IsCadlag (X n))
    (hU : ∀ T, 0 ≤ T → TendstoUniformlyOn X x atTop (Set.Icc 0 T)) :
    ReedGGN.Regulator.IsCadlag x := by
  constructor
  · intro t ht
    have h1 : TendstoUniformlyOnFilter X x atTop (𝓝[≥] t) :=
      (hU (t + 1) (by linarith)).tendstoUniformlyOnFilter.mono_right
        (le_principal_iff.mpr (mem_of_superset (Icc_mem_nhdsGE (show t < t + 1 by linarith))
          (Set.Icc_subset_Icc_left ht)))
    exact h1.tendsto_of_eventually_tendsto (Eventually.of_forall fun n => (hX n).1 t ht)
      ((hU t ht).tendsto_at ⟨ht, le_rfl⟩)
  · intro t ht
    choose L hL using fun n => (hX n).2 t ht
    have hUt := hU t ht.le
    have hC : CauchySeq L := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := eventually_atTop.mp (Metric.tendstoUniformlyOn_iff.mp hUt (ε / 4) (by linarith))
      refine ⟨N, fun m hm n hn => ?_⟩
      have hlim : Tendsto (fun s => X m s - X n s) (𝓝[<] t) (𝓝 (L m - L n)) := (hL m).sub (hL n)
      have hb : ∀ᶠ s in 𝓝[<] t, |X m s - X n s| ≤ ε / 2 := by
        filter_upwards [Ioo_mem_nhdsLT ht] with s hs
        have h1 := hN m hm s ⟨hs.1.le, hs.2.le⟩
        have h2 := hN n hn s ⟨hs.1.le, hs.2.le⟩
        rw [Real.dist_eq] at h1 h2
        have := abs_sub_le (X m s) (x s) (X n s)
        rw [abs_sub_comm (X m s) (x s)] at this
        linarith
      have : |L m - L n| ≤ ε / 2 :=
        le_of_tendsto (continuous_abs.continuousAt.tendsto.comp hlim) hb
      rw [Real.dist_eq]; linarith
    obtain ⟨ℓ, hℓ⟩ := cauchySeq_tendsto_of_complete hC
    have h1 : TendstoUniformlyOnFilter X x atTop (𝓝[<] t) :=
      hUt.tendstoUniformlyOnFilter.mono_right
        (le_principal_iff.mpr (mem_of_superset (Ioo_mem_nhdsLT ht) Set.Ioo_subset_Icc_self))
    exact ⟨ℓ, h1.tendsto_of_eventually_tendsto (Eventually.of_forall hL) hℓ⟩

noncomputable def g46_X (μ : Measure ℝ) (y : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0 => y
  | n + 1 => fun s => y s + ∫ u in Set.Icc 0 s, max (g46_X μ y n (s - u)) 0 ∂μ

theorem g46_exist (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ0 : μ (Set.Iio 0) = 0)
    (hatom : μ {0} < 1) (ζ : ℝ → ℝ) (hζ : ReedGGN.Regulator.IsCadlag ζ) (β : ℝ) :
    ∃ q : ℝ → ℝ, ReedGGN.Regulator.IsCadlag q ∧ SolvesLimitEq μ ζ β q := by
  obtain ⟨y, hy⟩ : ∃ y : ℝ → ℝ, y = fun s => ζ (max s 0) - β * ReedGGN.Regulator.Fe μ s :=
    ⟨_, rfl⟩
  have hym : Measurable y := hy ▸
    (g46_rc_meas _ (g46_cad_rc ζ hζ)).sub (measurable_const.mul (g46_Fe_meas μ))
  have hyc : ReedGGN.Regulator.IsCadlag y := hy ▸ g46_cad_sub
    (g46_cad_congr hζ (fun s hs => by simp [max_eq_left hs])) (g46_cad_const_mul β (g46_Fe_cadlag μ))
  obtain ⟨X, hX⟩ : ∃ X : ℕ → ℝ → ℝ, X = g46_X μ y := ⟨_, rfl⟩
  have hX0 : X 0 = y := by rw [hX]; rfl
  have hXs : ∀ n, X (n + 1) = fun s => y s + ∫ u in Set.Icc 0 s, max (X n (s - u)) 0 ∂μ := by
    intro n; rw [hX]; rfl
  have hXm : ∀ n, Measurable (X n) := by
    intro n; induction n with
    | zero => rw [hX0]; exact hym
    | succ n ih => rw [hXs]; exact hym.add (g46_K_meas μ (ih.max measurable_const))
  have hXc : ∀ n, ReedGGN.Regulator.IsCadlag (X n) := by
    intro n; induction n with
    | zero => rw [hX0]; exact hyc
    | succ n ih =>
      rw [hXs]
      exact g46_cad_add hyc (g46_K_cadlag μ _ ((hXm n).max measurable_const) (g46_cad_max0 ih))
  have hXneg : ∀ n s, s < 0 → X n s = y s := by
    intro n s hs; cases n with
    | zero => rw [hX0]
    | succ n =>
      rw [hXs]
      simp [Set.Icc_eq_empty (show ¬ (0:ℝ) ≤ s by linarith)]
  obtain ⟨D, hD⟩ : ∃ D : ℕ → ℝ → ℝ, D = fun n s => X (n + 1) s - X n s := ⟨_, rfl⟩
  have hDm : ∀ n, Measurable (D n) := fun n => by rw [hD]; exact (hXm (n + 1)).sub (hXm n)
  have hDneg : ∀ n s, s < 0 → D n s = 0 := fun n s hs => by
    rw [hD]; simp only; rw [hXneg _ _ hs, hXneg _ _ hs, sub_self]
  have hDstep : ∀ n, ∀ t, 0 ≤ t → |D (n + 1) t| ≤ ∫ u in Set.Icc 0 t, |D n (t - u)| ∂μ := by
    intro n t ht
    have i1 := g46_intOn_lb μ ht (measure_lt_top _ _) ((hXm (n + 1)).max measurable_const)
      (g46_max_lb _ (g46_cad_lb _ (hXc (n + 1))))
    have i2 := g46_intOn_lb μ ht (measure_lt_top _ _) ((hXm n).max measurable_const)
      (g46_max_lb _ (g46_cad_lb _ (hXc n)))
    have i3 := g46_intOn_lb μ ht (measure_lt_top _ _) (hDm n)
      (g46_cad_lb _ (by rw [hD]; exact g46_cad_sub (hXc (n + 1)) (hXc n)))
    have e : D (n + 1) t = ∫ u in Set.Icc 0 t, (max (X (n + 1) (t - u)) 0 - max (X n (t - u)) 0) ∂μ := by
      rw [integral_sub i1 i2, hD]; simp only; rw [hXs (n + 1), hXs n]; ring
    rw [e]
    refine abs_integral_le_integral_abs.trans ?_
    apply setIntegral_mono_on (i1.sub i2).abs i3.abs measurableSet_Icc
    intro u _
    rw [hD]
    exact abs_max_sub_max_le_abs _ _ _
  -- bounds
  have hbound : ∀ T, 0 ≤ T → ∃ C, ∀ n, ∀ t ∈ Set.Icc 0 T,
      |D n t| ≤ C * (convPow μ n (Set.Iic T)).toReal ∧ 0 ≤ C := by
    intro T hT
    obtain ⟨C, hC⟩ := g46_cad_lb _ (show ReedGGN.Regulator.IsCadlag (D 0) by
      rw [hD]; exact g46_cad_sub (hXc 1) (hXc 0)) T hT
    have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0 ⟨le_rfl, hT⟩)
    have hit := g46_iter μ hμ0 D hDm T C hC (fun n t ht => hDstep n t ht.1)
    refine ⟨C, fun n t ht => ⟨(hit n t ht).trans ?_, hC0⟩⟩
    apply mul_le_mul_of_nonneg_left _ hC0
    haveI := g46_convPow_prob μ n
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.Iic_subset_Iic.mpr ht.2))
  obtain ⟨x, hx⟩ : ∃ x : ℝ → ℝ, x = fun s => y s + ∑' n, D n s := ⟨_, rfl⟩
  have hpart : ∀ N s, X N s = y s + ∑ n ∈ Finset.range N, D n s := by
    intro N s
    rw [hD]; simp only
    rw [Finset.sum_range_sub (fun n => X n s), hX0]; ring
  have hU : ∀ T, 0 ≤ T → TendstoUniformlyOn X x atTop (Set.Icc 0 T) := by
    intro T hT
    obtain ⟨C, hC⟩ := hbound T hT
    have hsum : Summable (fun n => C * (convPow μ n (Set.Iic T)).toReal) :=
      (ENNReal.summable_toReal (g46_tsum_fin μ hμ0 hatom T)).mul_left C
    have hM := tendstoUniformlyOn_tsum_nat hsum (f := D) (s := Set.Icc 0 T)
      (fun n t ht => by rw [Real.norm_eq_abs]; exact (hC n t ht).1)
    rw [Metric.tendstoUniformlyOn_iff] at hM ⊢
    intro ε hε
    filter_upwards [hM ε hε] with N hN
    intro s hs
    rw [hx, hpart N s]
    simp only
    rw [dist_add_left]; exact hN s hs
  have hpt : ∀ s, Tendsto (fun N => X N s) atTop (𝓝 (x s)) := by
    intro s
    rcases lt_or_ge s 0 with hs | hs
    · have : x s = y s := by rw [hx]; simp [hDneg _ s hs]
      rw [this]
      exact tendsto_const_nhds.congr (fun N => (hXneg N s hs).symm)
    · exact (hU s hs).tendsto_at ⟨hs, le_rfl⟩
  have hxm : Measurable x := measurable_of_tendsto_metrizable hXm (tendsto_pi_nhds.mpr hpt)
  have hxc : ReedGGN.Regulator.IsCadlag x := g46_unif_cadlag X x hXc hU
  refine ⟨x, hxc, fun t ht => ?_⟩
  -- pass to the limit in X (N+1) t = y t + ∫ max (X N (t-u)) 0
  obtain ⟨B, hB⟩ := g46_cad_lb x hxc t ht
  have hev : ∀ᶠ N in atTop, ∀ s ∈ Set.Icc 0 t, |X N s| ≤ B + 1 := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hU t ht) 1 one_pos] with N hN
    intro s hs
    have h1 := hN s hs
    rw [Real.dist_eq] at h1
    have := abs_sub_abs_le_abs_sub (X N s) (x s)
    rw [abs_sub_comm] at h1
    linarith [hB s hs]
  have hlimR : Tendsto (fun N => ∫ u in Set.Icc 0 t, max (X N (t - u)) 0 ∂μ) atTop
      (𝓝 (∫ u in Set.Icc 0 t, max (x (t - u)) 0 ∂μ)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => B + 1)
    · exact Eventually.of_forall (fun N =>
        (((hXm N).comp (measurable_const.sub measurable_id)).max measurable_const).aestronglyMeasurable)
    · filter_upwards [hev] with N hN
      refine ae_restrict_of_forall_mem measurableSet_Icc (fun u hu => ?_)
      have := hN (t - u) ⟨by linarith [hu.2], by linarith [hu.1]⟩
      rw [Real.norm_eq_abs]
      rcases le_total (X N (t - u)) 0 with h | h
      · rw [max_eq_right h, abs_zero]; exact (abs_nonneg _).trans this
      · rw [max_eq_left h]; exact this
    · exact integrable_const _
    · exact Eventually.of_forall (fun u => (hpt (t - u)).max tendsto_const_nhds)
  have hlimL : Tendsto (fun N => X (N + 1) t) atTop (𝓝 (x t)) :=
    (hpt t).comp (tendsto_add_atTop_nat 1)
  have heqN : (fun N => X (N + 1) t) = fun N => y t + ∫ u in Set.Icc 0 t, max (X N (t - u)) 0 ∂μ := by
    funext N; rw [hXs N]
  rw [heqN] at hlimL
  have := tendsto_nhds_unique hlimL (tendsto_const_nhds.add hlimR)
  rw [this, hy]
  simp only [max_eq_left ht]

theorem g46_cor (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hint : Integrable id μ) (hmean : ∫ x, x ∂μ = 1)
    (ζ : ℝ → ℝ) (hζ : ReedGGN.Regulator.IsCadlag ζ) (β : ℝ) :
    (∀ q : ℝ → ℝ, ReedGGN.Regulator.IsCadlag q → (SolvesLimitEq μ ζ β q ↔ SolvesRenewalEq μ ζ β q)) ∧
    ∃ q : ℝ → ℝ, ReedGGN.Regulator.IsCadlag q ∧ SolvesRenewalEq μ ζ β q ∧
      ∀ q' : ℝ → ℝ, ReedGGN.Regulator.IsCadlag q' → SolvesRenewalEq μ ζ β q' → Set.EqOn q' q (Set.Ici 0) := by
  have hatom := g46_atom_of_mean μ hmean
  have hequiv := g46_equiv μ hμ0 hint hmean ζ hζ β
  obtain ⟨x, hxc, hxsol⟩ := g46_exist μ hμ0 hatom ζ hζ β
  refine ⟨hequiv, x, hxc, (hequiv x hxc).mp hxsol, fun q' hq' hren => ?_⟩
  exact g46_lim_uniq μ hμ0 hatom ζ hζ β q' x hq' hxc ((hequiv q' hq').mpr hren) hxsol

end ReedGGN.RenewalRep

open ReedGGN.RenewalRep


theorem solution (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ0 : μ (Set.Iio 0) = 0) (hint : Integrable id μ) (hmean : ∫ x, x ∂μ = 1)
    (ζ : ℝ → ℝ) (hζ : ReedGGN.Regulator.IsCadlag ζ) (β : ℝ) :
    (∀ q : ℝ → ℝ, ReedGGN.Regulator.IsCadlag q → (SolvesLimitEq μ ζ β q ↔ SolvesRenewalEq μ ζ β q)) ∧
    ∃ q : ℝ → ℝ, ReedGGN.Regulator.IsCadlag q ∧ SolvesRenewalEq μ ζ β q ∧
      ∀ q' : ℝ → ℝ, ReedGGN.Regulator.IsCadlag q' → SolvesRenewalEq μ ζ β q' → Set.EqOn q' q (Set.Ici 0) := by
  exact g46_cor μ hμ0 hint hmean ζ hζ β
