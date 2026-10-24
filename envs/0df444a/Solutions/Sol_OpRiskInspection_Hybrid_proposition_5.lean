-- Prove2me | solution 1 for OpRiskInspection.Hybrid.proposition_5
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-23T11:55:54.592288+00:00
-- url     : https://prove2.me/submissions/35ec5d35-b1f1-4009-b909-3b9893275c90

import Mathlib
import Definitions.Def_OpRiskInspection_RandomVsPeriodic_Setting

set_option autoImplicit false

namespace OpRiskInspection.Hybrid.P5

open MeasureTheory Set
open scoped ENNReal

/-- Tonelli over the triangle `0 < t < τ`. -/
lemma tri_lintegral (μ : Measure ℝ) [SFinite μ] (f g : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ τ, (∫⁻ t in Ioo 0 τ, f t) * g τ ∂μ = ∫⁻ t in Ioi 0, f t * ∫⁻ τ in Ioi t, g τ ∂μ := by
  have hS : MeasurableSet {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_fst)
  have key : ∀ τ t : ℝ, (Ioo 0 τ).indicator f t * g τ =
      {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1}.indicator (fun p => f p.2 * g p.1) (τ, t) := by
    intro τ t
    by_cases h : 0 < t ∧ t < τ
    · rw [indicator_of_mem (show t ∈ Ioo 0 τ from h),
        indicator_of_mem (show (τ, t) ∈ {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1} from h)]
    · rw [indicator_of_notMem (show t ∉ Ioo 0 τ from h),
        indicator_of_notMem (show (τ, t) ∉ {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1} from h), zero_mul]
  have hmeas : Measurable ({p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1}.indicator
      (fun p : ℝ × ℝ => f p.2 * g p.1)) :=
    ((hf.comp measurable_snd).mul (hg.comp measurable_fst)).indicator hS
  calc ∫⁻ τ, (∫⁻ t in Ioo 0 τ, f t) * g τ ∂μ
      = ∫⁻ τ, ∫⁻ t, {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1}.indicator
          (fun p => f p.2 * g p.1) (τ, t) ∂volume ∂μ := by
        refine lintegral_congr fun τ => ?_
        rw [← lintegral_indicator measurableSet_Ioo,
          ← lintegral_mul_const _ (hf.indicator measurableSet_Ioo)]
        exact lintegral_congr fun t => key τ t
    _ = ∫⁻ t, ∫⁻ τ, {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1}.indicator
          (fun p => f p.2 * g p.1) (τ, t) ∂μ ∂volume :=
        lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ t, (Ioi 0).indicator (fun t => f t * ∫⁻ τ in Ioi t, g τ ∂μ) t := by
        refine lintegral_congr fun t => ?_
        by_cases ht : 0 < t
        · rw [indicator_of_mem (show t ∈ Ioi (0:ℝ) from ht), ← lintegral_const_mul _ hg,
            ← lintegral_indicator measurableSet_Ioi]
          refine lintegral_congr fun τ => ?_
          by_cases hτ : t < τ
          · rw [indicator_of_mem (show (τ, t) ∈ {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1} from ⟨ht, hτ⟩),
              indicator_of_mem (show τ ∈ Ioi t from hτ)]
          · rw [indicator_of_notMem (show (τ, t) ∉ {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1} from
              fun h => hτ h.2), indicator_of_notMem (show τ ∉ Ioi t from hτ)]
        · rw [indicator_of_notMem (show t ∉ Ioi (0:ℝ) from ht)]
          refine (lintegral_congr fun τ => ?_).trans lintegral_zero
          exact indicator_of_notMem (fun h => ht h.1) _
    _ = _ := lintegral_indicator measurableSet_Ioi _

/-- Real form of the triangle swap, for a measure carried by `(0, ∞)`. -/
lemma tri_swap (μ : Measure ℝ) [SFinite μ] (hμ : μ (Iic 0) = 0) (h k : ℝ → ℝ)
    (hh : Measurable h) (hk : Measurable k) (h0 : ∀ t, 0 ≤ t → 0 ≤ h t) (k0 : ∀ τ, 0 ≤ k τ)
    (hloc : ∀ a b, IntervalIntegrable h volume a b)
    (hkint : ∀ t, IntegrableOn k (Ioi t) μ) :
    ∫ τ, (∫ t in (0 : ℝ)..τ, h t) * k τ ∂μ = ∫ t in Ioi 0, h t * ∫ τ in Ioi t, k τ ∂μ := by
  have hpos : ∀ᵐ τ ∂μ, 0 < τ := by
    rw [ae_iff]
    have : {a : ℝ | ¬ 0 < a} = Iic 0 := by ext a; simp
    rw [this]; exact hμ
  have hprim : Continuous fun τ => ∫ t in (0 : ℝ)..τ, h t :=
    intervalIntegral.continuous_primitive hloc 0
  have hI_anti : Antitone fun t => ∫ τ in Ioi t, k τ ∂μ := by
    intro s t hst
    exact setIntegral_mono_set (hkint s) (Filter.Eventually.of_forall fun τ => k0 τ)
      (Filter.Eventually.of_forall (Ioi_subset_Ioi hst))
  rw [integral_eq_lintegral_of_nonneg_ae, integral_eq_lintegral_of_nonneg_ae]
  · congr 1
    refine (lintegral_congr_ae ?_).trans ((tri_lintegral μ (fun t => ENNReal.ofReal (h t))
      (fun τ => ENNReal.ofReal (k τ))
      (ENNReal.measurable_ofReal.comp hh) (ENNReal.measurable_ofReal.comp hk)).trans ?_)
    · 
      filter_upwards [hpos] with τ hτ
      rw [intervalIntegral.integral_of_le hτ.le, integral_Ioc_eq_integral_Ioo,
        ENNReal.ofReal_mul (setIntegral_nonneg measurableSet_Ioo fun t ht => h0 t ht.1.le),
        ofReal_integral_eq_lintegral_ofReal]
      · exact (hloc 0 τ).1.mono_set Ioo_subset_Ioc_self
      · exact (ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall fun t ht => h0 t ht.1.le)
    · refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      rw [ENNReal.ofReal_mul (h0 t (le_of_lt ht)), ofReal_integral_eq_lintegral_ofReal (hkint t)
        (Filter.Eventually.of_forall fun τ => k0 τ)]
  · exact (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun t ht =>
      mul_nonneg (h0 t (le_of_lt ht)) (setIntegral_nonneg measurableSet_Ioi fun τ _ => k0 τ))
  · exact (hh.mul hI_anti.measurable).aestronglyMeasurable
  · filter_upwards [hpos] with τ hτ
    exact mul_nonneg (intervalIntegral.integral_nonneg hτ.le fun t ht => h0 t ht.1) (k0 τ)
  · exact (hprim.measurable.mul hk).aestronglyMeasurable

open OpRiskInspection.RandomVsPeriodic

lemma intervalIntegrable_of_bdd (f : ℝ → ℝ) (hf : Measurable f) (C : ℝ)
    (hC : ∀ t, |f t| ≤ C) (a b : ℝ) : IntervalIntegrable f volume a b := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  refine IntervalIntegrable.mono_fun (intervalIntegrable_const (c := C)) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  simpa [Real.norm_eq_abs, abs_of_nonneg hC0] using hC t

lemma expCount_continuous (p : Params) (a : Effort) (ha : Admissible a) :
    Continuous (expCount p a) := by
  unfold expCount
  refine continuous_const.mul (intervalIntegral.continuous_primitive (fun x y => ?_) 0)
  refine intervalIntegrable_of_bdd _ (Real.measurable_exp.comp ha.1.neg) 1 (fun t => ?_) x y
  show |Real.exp (-(a t))| ≤ 1
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.2 (neg_nonpos.2 (ha.2.1 t))

lemma expCount_nonneg (p : Params) (hp : Standing p) (a : Effort) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ expCount p a t :=
  mul_nonneg hp.hlam.le (intervalIntegral.integral_nonneg ht fun _ _ => (Real.exp_pos _).le)

/-- Survival weight `F (t, ∞)`. -/
noncomputable def Sv (F : Measure ℝ) (t : ℝ) : ℝ := ∫ τ in Ioi t, (1 : ℝ) ∂F

/-- Discounted survival weight `E[e^{-rτ}; τ > t]`. -/
noncomputable def Qv (p : Params) (F : Measure ℝ) (t : ℝ) : ℝ :=
  ∫ τ in Ioi t, Real.exp (-(p.r * τ)) ∂F

lemma Sv_nonneg (F : Measure ℝ) (t : ℝ) : 0 ≤ Sv F t :=
  setIntegral_nonneg measurableSet_Ioi fun _ _ => zero_le_one

lemma Sv_le_one (F : Measure ℝ) [IsProbabilityMeasure F] (t : ℝ) : Sv F t ≤ 1 := by
  unfold Sv
  rw [setIntegral_const, smul_eq_mul, mul_one]
  exact measureReal_le_one

lemma Sv_anti (F : Measure ℝ) [IsProbabilityMeasure F] : Antitone (Sv F) := by
  intro s t hst
  exact setIntegral_mono_set (integrableOn_const) (Filter.Eventually.of_forall fun _ => zero_le_one)
    (Filter.Eventually.of_forall (Ioi_subset_Ioi hst))

lemma effortInt_eq (p : Params) (F : Measure ℝ) [IsProbabilityMeasure F] (hF : F (Iic 0) = 0)
    (a : Effort) (ha : Admissible a) :
    effortInt p F a = ∫ t in Ioi 0, a t * Real.exp (-(p.r * t)) * Sv F t := by
  obtain ⟨hm, h0, B, hB⟩ := ha
  have := tri_swap F hF (fun t => a t * Real.exp (-(p.r * t))) (fun _ => 1)
    (hm.mul (Real.measurable_exp.comp (measurable_const.mul measurable_id).neg)) measurable_const
    (fun t _ => mul_nonneg (h0 t) (Real.exp_pos _).le) (fun _ => zero_le_one) ?_
    (fun t => integrableOn_const)
  · simpa [effortInt, Sv] using this
  · intro x y
    refine (intervalIntegrable_of_bdd a hm B (fun t => by rw [abs_of_nonneg (h0 t)]; exact hB t)
      x y).mul_continuousOn ?_
    exact (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousOn

lemma measurable_exp_neg_a (a : Effort) (ha : Admissible a) :
    Measurable fun t => Real.exp (-(a t)) := Real.measurable_exp.comp ha.1.neg

lemma exp_neg_a_intervalIntegrable (a : Effort) (ha : Admissible a) (x y : ℝ) :
    IntervalIntegrable (fun t => Real.exp (-(a t))) volume x y := by
  refine intervalIntegrable_of_bdd _ (measurable_exp_neg_a a ha) 1 (fun t => ?_) x y
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.2 (neg_nonpos.2 (ha.2.1 t))

lemma measurable_exp_neg_r (r : ℝ) : Measurable fun t : ℝ => Real.exp (-(r * t)) :=
  Real.measurable_exp.comp (measurable_const.mul measurable_id).neg

lemma integrableOn_exp_neg_r (F : Measure ℝ) [IsFiniteMeasure F] {r : ℝ} (hr : 0 < r) (t : ℝ) :
    IntegrableOn (fun τ => Real.exp (-(r * τ))) (Ioi t) F := by
  refine Integrable.of_bound (measurable_exp_neg_r r).aestronglyMeasurable (Real.exp (-(r * t)))
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun τ hτ => ?_))
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 (by nlinarith [mem_Ioi.mp hτ])

lemma penaltyInt_eq (p : Params) (hp : Standing p) (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : F (Iic 0) = 0) (a : Effort) (ha : Admissible a) :
    penaltyInt p F a = p.lam * ∫ t in Ioi 0, Real.exp (-(a t)) * Qv p F t := by
  have e1 : penaltyInt p F a = p.lam * ∫ τ, (∫ t in (0:ℝ)..τ, Real.exp (-(a t))) *
      Real.exp (-(p.r * τ)) ∂F := by
    rw [penaltyInt, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
    simp only [expCount]; ring
  rw [e1, tri_swap F hF (fun t => Real.exp (-(a t))) (fun τ => Real.exp (-(p.r * τ)))
    (measurable_exp_neg_a a ha) (measurable_exp_neg_r _)
    (fun t _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le)
    (exp_neg_a_intervalIntegrable a ha) (integrableOn_exp_neg_r F hp.hr)]
  rfl

/-- Discounted survival integral `∫_{s}^{∞} e^{-rt} S(t) dt`. -/
noncomputable def Wv (p : Params) (F : Measure ℝ) (s : ℝ) : ℝ :=
  ∫ t in Ioi s, Real.exp (-(p.r * t)) * Sv F t ∂(volume.restrict (Ioi 0))

lemma lossInt_eq (p : Params) (hp : Standing p) (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : F (Iic 0) = 0) (a : Effort) (ha : Admissible a) :
    lossInt p F a = p.lam * ∫ s in Ioi 0, Real.exp (-(a s)) * Wv p F s := by
  have hcont := expCount_continuous p a ha
  have hSm : Measurable (Sv F) := (Sv_anti F).measurable
  have e1 := tri_swap F hF (fun t => expCount p a t * Real.exp (-(p.r * t))) (fun _ => 1)
    (hcont.measurable.mul (measurable_exp_neg_r _)) measurable_const
    (fun t ht => mul_nonneg (expCount_nonneg p hp a ht) (Real.exp_pos _).le)
    (fun _ => zero_le_one)
    (fun x y => (hcont.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id).neg)).intervalIntegrable x y)
    (fun t => integrableOn_const)
  simp only [mul_one] at e1
  have hμ : (volume.restrict (Ioi (0:ℝ))) (Iic 0) = 0 := by
    rw [Measure.restrict_apply measurableSet_Iic, Iic_inter_Ioi]; simp
  have e2 := tri_swap (volume.restrict (Ioi (0:ℝ))) hμ (fun t => Real.exp (-(a t)))
    (fun t => Real.exp (-(p.r * t)) * Sv F t) (measurable_exp_neg_a a ha)
    ((measurable_exp_neg_r _).mul hSm) (fun t _ => (Real.exp_pos _).le)
    (fun t => mul_nonneg (Real.exp_pos _).le (Sv_nonneg F t))
    (exp_neg_a_intervalIntegrable a ha) ?_
  · calc lossInt p F a = ∫ t in Ioi 0, expCount p a t * Real.exp (-(p.r * t)) * Sv F t := by
          rw [lossInt]; simpa [Sv] using e1
      _ = p.lam * ∫ t in Ioi 0, (∫ s in (0:ℝ)..t, Real.exp (-(a s))) *
            (Real.exp (-(p.r * t)) * Sv F t) := by
          rw [← integral_const_mul]; congr 1; funext t; simp only [expCount]; ring
      _ = _ := by rw [e2]; rfl
  · intro s
    rw [IntegrableOn, Measure.restrict_restrict measurableSet_Ioi]
    have hg : IntegrableOn (fun t : ℝ => Real.exp (-(p.r * t))) (Ioi 0) := by
      simpa [neg_mul] using integrableOn_exp_mul_Ioi (neg_neg_of_pos hp.hr) 0
    refine Integrable.mono' (hg.mono_set inter_subset_right)
      ((measurable_exp_neg_r _).mul hSm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (Sv_nonneg F t))]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (Sv_le_one F t)

/-! ### The exponential law -/

lemma integral_expMeasure {v : ℝ} (hv : 0 < v) (g : ℝ → ℝ) :
    ∫ x, g x ∂(ProbabilityTheory.expMeasure v) =
      ∫ x in Ici 0, v * Real.exp (-(v * x)) * g x := by
  rw [ProbabilityTheory.expMeasure, ProbabilityTheory.gammaMeasure,
    integral_withDensity_eq_integral_toReal_smul
      (show Measurable (ProbabilityTheory.gammaPDF 1 v) from
        (ProbabilityTheory.measurable_gammaPDFReal 1 v).ennreal_ofReal)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    ← integral_indicator measurableSet_Ici]
  congr 1; funext x
  by_cases hx : 0 ≤ x
  · rw [indicator_of_mem (show x ∈ Ici (0:ℝ) from hx)]
    simp [ProbabilityTheory.gammaPDF, ProbabilityTheory.gammaPDFReal, hx,
      ENNReal.toReal_ofReal (mul_nonneg hv.le (Real.exp_pos _).le)]
  · rw [indicator_of_notMem (show x ∉ Ici (0:ℝ) from hx)]
    simp [ProbabilityTheory.gammaPDF, ProbabilityTheory.gammaPDFReal, hx]

lemma expMeasure_Iic_zero {v : ℝ} (hv : 0 < v) :
    ProbabilityTheory.expMeasure v (Iic 0) = 0 := by
  have := ProbabilityTheory.isProbabilityMeasure_expMeasure hv
  have h := ProbabilityTheory.cdf_expMeasure_eq hv 0
  rw [ProbabilityTheory.cdf_eq_real] at h
  simp only [le_refl, if_true, mul_zero, neg_zero, Real.exp_zero, sub_self] at h
  exact (measureReal_eq_zero_iff).1 h

lemma integral_exp_neg_Ioi_mul {ρ : ℝ} (hρ : 0 < ρ) (t : ℝ) :
    ∫ x in Ioi t, Real.exp (-(ρ * x)) = Real.exp (-(ρ * t)) / ρ := by
  have := integral_exp_mul_Ioi (neg_neg_of_pos hρ) t
  simp only [neg_mul] at this
  rw [this, neg_div_neg_eq]

lemma discF_random (p : Params) (hp : Standing p) {v : ℝ} (hv : 0 < v) :
    discF p (randomLaw v) = v / (p.r + v) := by
  have hρ : 0 < p.r + v := add_pos hp.hr hv
  rw [discF, randomLaw, integral_expMeasure hv, integral_Ici_eq_integral_Ioi]
  have : (fun x => v * Real.exp (-(v * x)) * Real.exp (-(p.r * x))) =
      fun x => v * Real.exp (-((p.r + v) * x)) := by
    funext x; rw [mul_assoc, ← Real.exp_add]; ring_nf
  rw [this, integral_const_mul, integral_exp_neg_Ioi_mul hρ]
  simp [div_eq_mul_inv]

lemma Sv_random {v : ℝ} (hv : 0 < v) {t : ℝ} (ht : 0 ≤ t) :
    Sv (randomLaw v) t = Real.exp (-(v * t)) := by
  have := ProbabilityTheory.isProbabilityMeasure_expMeasure hv
  have h := ProbabilityTheory.cdf_expMeasure_eq hv t
  rw [ProbabilityTheory.cdf_eq_real, if_pos ht] at h
  rw [Sv, randomLaw, setIntegral_const, smul_eq_mul, mul_one, ← compl_Iic,
    measureReal_compl measurableSet_Iic, probReal_univ, h]
  ring

lemma Qv_random (p : Params) (hp : Standing p) {v : ℝ} (hv : 0 < v) {t : ℝ} (ht : 0 ≤ t) :
    Qv p (randomLaw v) t = v / (p.r + v) * Real.exp (-((p.r + v) * t)) := by
  have hρ : 0 < p.r + v := add_pos hp.hr hv
  rw [Qv, randomLaw, ← integral_indicator measurableSet_Ioi, integral_expMeasure hv,
    ← integral_indicator measurableSet_Ici]
  have hpt : ∀ x, (Ici 0).indicator (fun x => v * Real.exp (-(v * x)) *
      (Ioi t).indicator (fun τ => Real.exp (-(p.r * τ))) x) x =
      (Ioi t).indicator (fun x => v * Real.exp (-((p.r + v) * x))) x := by
    intro x
    by_cases hx : t < x
    · have hx0 : 0 ≤ x := ht.trans hx.le
      rw [indicator_of_mem (show x ∈ Ici (0:ℝ) from hx0),
        indicator_of_mem (show x ∈ Ioi t from hx), indicator_of_mem (show x ∈ Ioi t from hx)]
      rw [mul_assoc, ← Real.exp_add]; ring_nf
    · rw [indicator_of_notMem (show x ∉ Ioi t from hx)]
      by_cases hx0 : 0 ≤ x
      · rw [indicator_of_mem (show x ∈ Ici (0:ℝ) from hx0),
          indicator_of_notMem (show x ∉ Ioi t from hx)]
        simp
      · rw [indicator_of_notMem (show x ∉ Ici (0:ℝ) from hx0)]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_indicator measurableSet_Ioi,
    integral_const_mul, integral_exp_neg_Ioi_mul hρ]
  field_simp

lemma Wv_random (p : Params) (hp : Standing p) {v : ℝ} (hv : 0 < v) {s : ℝ} (hs : 0 ≤ s) :
    Wv p (randomLaw v) s = Real.exp (-((p.r + v) * s)) / (p.r + v) := by
  have hρ : 0 < p.r + v := add_pos hp.hr hv
  rw [Wv, Measure.restrict_restrict measurableSet_Ioi,
    Ioi_inter_Ioi, show s ⊔ 0 = s from max_eq_left hs, ← integral_exp_neg_Ioi_mul hρ]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [Sv_random hv (hs.trans (le_of_lt ht)), ← Real.exp_add]; ring_nf

/-! ### Participation -/

lemma principal_le_reduced (p : Params) (K v : ℝ) (F : Measure ℝ) (a : Effort) (P w : ℝ)
    (hδ : discF p F < 1) (hr : 0 < p.r)
    (hpart : p.pibar ≤ agentPayoff p F a P w) :
    principalPayoff p K v F a P w ≤ reducedPayoff p K v F a := by
  have h1 : 0 < 1 - discF p F := by linarith
  unfold agentPayoff at hpart
  unfold principalPayoff reducedPayoff mubar
  have e : (p.mu - p.r * p.pibar) / p.r = p.mu / p.r - p.pibar := by field_simp
  rw [e, sub_div]
  linarith

/-! ### First-best bound for the random policy -/

/-- `min_{a ≥ 0} (c a + B e^{-a})`. -/
noncomputable def mfun (c B : ℝ) : ℝ := if c < B then c * (1 + Real.log (B / c)) else B

lemma mfun_le {c B : ℝ} (hc : 0 < c) (hB : 0 < B) {a : ℝ} (ha : 0 ≤ a) :
    mfun c B ≤ c * a + B * Real.exp (-a) := by
  unfold mfun
  split_ifs with h
  · have e : B * Real.exp (-a) = c * Real.exp (Real.log (B / c) - a) := by
      rw [Real.exp_sub, Real.exp_log (div_pos hB hc)]; field_simp; rw [Real.exp_neg]; field_simp
    rw [e]
    have := Real.add_one_le_exp (Real.log (B / c) - a)
    nlinarith
  · push Not at h
    have := Real.add_one_le_exp (-a)
    nlinarith [Real.exp_pos (-a)]

/-- The first-best random payoff bound `G(v)`. -/
noncomputable def Grand (p : Params) (K v : ℝ) : ℝ :=
  mubar p / p.r - mfun p.c (p.L * p.lam / (p.r + v)) / p.r - K / (Real.exp (p.r / v) - 1)

lemma integrableOn_exp_neg_Ioi_zero {ρ : ℝ} (hρ : 0 < ρ) :
    IntegrableOn (fun t : ℝ => Real.exp (-(ρ * t))) (Ioi 0) := by
  simpa [neg_mul] using integrableOn_exp_mul_Ioi (neg_neg_of_pos hρ) 0

lemma random_reduced_le (p : Params) (hp : Standing p) (K : ℝ) {v : ℝ} (hv : 0 < v)
    (a : Effort) (ha : Admissible a) :
    reducedPayoff p K v (randomLaw v) a ≤ Grand p K v := by
  have : IsProbabilityMeasure (randomLaw v) := ProbabilityTheory.isProbabilityMeasure_expMeasure hv
  have hF : randomLaw v (Iic 0) = 0 := expMeasure_Iic_zero hv
  set ρ := p.r + v with hρdef
  have hρ : 0 < ρ := add_pos hp.hr hv
  obtain ⟨hm, h0, B, hB⟩ := ha
  have hg := integrableOn_exp_neg_Ioi_zero hρ
  have i1 : IntegrableOn (fun t => a t * Real.exp (-(ρ * t))) (Ioi 0) := by
    refine Integrable.mono' (hg.const_mul B) (hm.mul (measurable_exp_neg_r ρ)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (h0 t) (Real.exp_pos _).le)]
    exact mul_le_mul_of_nonneg_right (hB t) (Real.exp_pos _).le
  have i2 : IntegrableOn (fun t => Real.exp (-(a t)) * Real.exp (-(ρ * t))) (Ioi 0) := by
    refine Integrable.mono' hg ((measurable_exp_neg_a a ⟨hm, h0, B, hB⟩).mul
      (measurable_exp_neg_r ρ)).aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)]
    exact mul_le_of_le_one_left (Real.exp_pos _).le
      (Real.exp_le_one_iff.2 (neg_nonpos.2 (h0 t)))
  have hE : effortInt p (randomLaw v) a = ∫ t in Ioi 0, a t * Real.exp (-(ρ * t)) := by
    rw [effortInt_eq p _ hF a ⟨hm, h0, B, hB⟩]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [Sv_random hv (le_of_lt ht), mul_assoc, ← Real.exp_add, hρdef]; ring_nf
  have hL : lossInt p (randomLaw v) a =
      p.lam / ρ * ∫ t in Ioi 0, Real.exp (-(a t)) * Real.exp (-(ρ * t)) := by
    rw [lossInt_eq p hp _ hF a ⟨hm, h0, B, hB⟩, div_eq_mul_inv, mul_assoc,
      ← integral_const_mul (ρ⁻¹)]
    congr 1
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    rw [Wv_random p hp hv (le_of_lt ht)]; ring
  set m := mfun p.c (p.L * p.lam / ρ)
  have hBp : 0 < p.L * p.lam / ρ := div_pos (mul_pos hp.hL hp.hlam) hρ
  have key : m / ρ ≤ p.c * effortInt p (randomLaw v) a + p.L * lossInt p (randomLaw v) a := by
    have e1 : m / ρ = ∫ t in Ioi 0, m * Real.exp (-(ρ * t)) := by
      rw [integral_const_mul, integral_exp_neg_Ioi_mul hρ]; simp [div_eq_mul_inv]
    have e2 : p.c * effortInt p (randomLaw v) a + p.L * lossInt p (randomLaw v) a =
        ∫ t in Ioi 0, (p.c * (a t * Real.exp (-(ρ * t))) +
          p.L * p.lam / ρ * (Real.exp (-(a t)) * Real.exp (-(ρ * t)))) := by
      rw [integral_add (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul,
        hE, hL]; ring
    rw [e1, e2]
    refine setIntegral_mono_on (hg.const_mul m) ((i1.const_mul _).add (i2.const_mul _))
      measurableSet_Ioi fun t _ => ?_
    have := mfun_le hp.hc hBp (h0 t)
    have he := (Real.exp_pos (-(ρ * t))).le
    nlinarith
  have hδ : 1 - discF p (randomLaw v) = p.r / ρ := by
    rw [discF_random p hp hv, hρdef, eq_div_iff hρ.ne', sub_mul, div_mul_cancel₀ _ hρ.ne']; ring
  unfold reducedPayoff Grand
  rw [hδ]
  have e3 : p.c * effortInt p (randomLaw v) a / (p.r / ρ) + p.L * lossInt p (randomLaw v) a / (p.r / ρ)
      = (p.c * effortInt p (randomLaw v) a + p.L * lossInt p (randomLaw v) a) * ρ / p.r := by
    field_simp
  have e4 : m / p.r ≤ (p.c * effortInt p (randomLaw v) a + p.L * lossInt p (randomLaw v) a) * ρ / p.r := by
    rw [div_le_div_iff_of_pos_right hp.hr]
    rw [div_le_iff₀ hρ] at key; linarith
  linarith

lemma random_le_Grand (p : Params) (hp : Standing p) (K x : ℝ)
    (hx : Achievable p K randomLaw x) : ∃ v, 0 < v ∧ x ≤ Grand p K v := by
  obtain ⟨v, P, w, a, hv, _, _, hopt, hpart, rfl⟩ := hx
  refine ⟨v, hv, (principal_le_reduced p K v _ a P w ?_ hp.hr hpart).trans
    (random_reduced_le p hp K hv a hopt.1)⟩
  rw [discF_random p hp hv, div_lt_one (add_pos hp.hr hv)]; linarith [hp.hr]

/-! ### `Grand` attains its maximum -/

lemma mfun_eq {c : ℝ} (hc : 0 < c) (B : ℝ) :
    mfun c B = c * (1 + Real.log (max B c / c)) - c + min B c := by
  unfold mfun
  split_ifs with h
  · rw [max_eq_left h.le, min_eq_right h.le]; ring
  · push Not at h
    rw [max_eq_right h, min_eq_left h, div_self hc.ne', Real.log_one]; ring

lemma mfun_mono {c : ℝ} (hc : 0 < c) : Monotone (mfun c) := by
  intro B1 B2 h
  rw [mfun_eq hc, mfun_eq hc]
  have h1 : Real.log (max B1 c / c) ≤ Real.log (max B2 c / c) :=
    Real.log_le_log (div_pos (lt_max_of_lt_right hc) hc)
      (div_le_div_of_nonneg_right (max_le_max h le_rfl) hc.le)
  have h2 := min_le_min h (le_refl c)
  nlinarith

lemma mfun_continuous {c : ℝ} (hc : 0 < c) : Continuous (mfun c) := by
  have : mfun c = fun B => c * (1 + Real.log (max B c / c)) - c + min B c := funext (mfun_eq hc)
  rw [this]
  refine ((continuous_const.mul (continuous_const.add
    (((continuous_id.max continuous_const).div_const c).log fun B =>
      (div_pos (lt_max_of_lt_right hc) hc).ne'))).sub continuous_const).add
    (continuous_id.min continuous_const)

lemma Kterm_continuousOn (r K : ℝ) (hr : 0 < r) :
    ContinuousOn (fun v : ℝ => K / (Real.exp (r / v) - 1)) (Ioi 0) := by
  refine continuousOn_const.div ((Real.continuous_exp.comp_continuousOn
    (continuousOn_const.div continuousOn_id fun v hv => (ne_of_gt hv))).sub continuousOn_const)
    fun v hv => ?_
  have h0 : 0 < r / v := div_pos hr hv
  have h1 := Real.add_one_lt_exp h0.ne'
  show Real.exp (r / v) - 1 ≠ 0
  exact ne_of_gt (by linarith)

lemma Grand_continuousOn (p : Params) (hp : Standing p) (K : ℝ) :
    ContinuousOn (Grand p K) (Ioi 0) := by
  unfold Grand
  refine (continuousOn_const.sub ((( mfun_continuous hp.hc).comp_continuousOn
    (continuousOn_const.div (continuousOn_const.add continuousOn_id) fun v hv =>
      (add_pos hp.hr hv).ne')).div_const _)).sub (Kterm_continuousOn p.r K hp.hr)

lemma Kterm_nonneg (r K : ℝ) (hr : 0 < r) (hK : 0 ≤ K) {v : ℝ} (hv : 0 < v) :
    0 ≤ K / (Real.exp (r / v) - 1) := by
  have h0 : 0 < r / v := div_pos hr hv
  have := Real.add_one_lt_exp h0.ne'
  exact div_nonneg hK (by linarith)

lemma Grand_max (p : Params) (hp : Standing p) (K : ℝ) (hK : 0 < K) :
    ∃ vs, 0 < vs ∧ ∀ v, 0 < v → Grand p K v ≤ Grand p K vs := by
  have hr := hp.hr; have hc := hp.hc
  have hLl : 0 < p.L * p.lam := mul_pos hp.hL hp.hlam
  -- asm1a: c < Lλ/r, i.e. r < Lλ/c
  have hgap : 0 < p.L * p.lam / p.c - p.r := by
    have := hp.asm1a
    rw [lt_div_iff₀ hr] at this
    rw [sub_pos, lt_div_iff₀ hc]; linarith
  -- a point beating the v → 0 limit
  set v1 := min p.r (min (p.c / (8 * K)) ((p.L * p.lam / p.c - p.r) / 2)) with hv1def
  have hv1 : 0 < v1 := lt_min hr (lt_min (by positivity) (by linarith))
  have hv1r : v1 ≤ p.r := min_le_left _ _
  have hv1c : v1 ≤ p.c / (8 * K) := (min_le_right _ _).trans (min_le_left _ _)
  have hv1g : v1 ≤ (p.L * p.lam / p.c - p.r) / 2 := (min_le_right _ _).trans (min_le_right _ _)
  set h : ℝ → ℝ := fun a => mubar p / p.r - mfun p.c (p.L * p.lam / (p.r + a)) / p.r with hhdef
  have hB1 : p.c < p.L * p.lam / (p.r + v1) := by
    rw [lt_div_iff₀ (by linarith)]
    have : p.r + v1 < p.L * p.lam / p.c := by linarith
    rw [lt_div_iff₀ hc] at this; linarith
  have hB0 : p.c < p.L * p.lam / (p.r + 0) := by rw [add_zero]; exact hp.asm1a
  have hbeat : h 0 < Grand p K v1 := by
    simp only [hhdef, Grand]
    unfold mfun
    rw [if_pos hB0, if_pos hB1]
    have hlog : v1 / (p.r + v1) ≤ Real.log ((p.r + v1) / p.r) := by
      have := Real.one_sub_inv_le_log_of_pos (div_pos (add_pos hr hv1) hr)
      rw [inv_div] at this
      have e : 1 - p.r / (p.r + v1) = v1 / (p.r + v1) := by field_simp; ring
      linarith
    have hsplit : Real.log (p.L * p.lam / (p.r + 0) / p.c) =
        Real.log (p.L * p.lam / (p.r + v1) / p.c) + Real.log ((p.r + v1) / p.r) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1; rw [add_zero]; field_simp
    have hy : 0 < p.r / v1 := div_pos hr hv1
    have hexp := Real.quadratic_le_exp_of_nonneg hy.le
    have hK1 : K / (Real.exp (p.r / v1) - 1) ≤ 2 * K * v1 ^ 2 / p.r ^ 2 := by
      rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
      have : (p.r / v1) ^ 2 / 2 ≤ Real.exp (p.r / v1) - 1 := by nlinarith
      have e : (p.r / v1) ^ 2 = p.r ^ 2 / v1 ^ 2 := by rw [div_pow]
      rw [e] at this
      rw [div_div, le_sub_iff_add_le, div_add' _ _ _ (by positivity), div_le_iff₀ (by positivity)] at this
      nlinarith [sq_nonneg v1]
    have hmain : 2 * K * v1 ^ 2 / p.r ^ 2 < p.c * (v1 / (p.r + v1)) / p.r := by
      have h8 : 8 * K * v1 ≤ p.c := by rw [le_div_iff₀ (by positivity)] at hv1c; linarith
      have hq : 2 * K * v1 * (p.r + v1) < p.c * p.r := by nlinarith [mul_pos hK hv1]
      have e : p.c * (v1 / (p.r + v1)) / p.r = p.c * v1 / ((p.r + v1) * p.r) := by
        field_simp
      rw [e, div_lt_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_lt_mul_of_pos_left hq (mul_pos hv1 hr)]
    rw [hsplit]
    have : p.c * Real.log ((p.r + v1) / p.r) / p.r ≥ p.c * (v1 / (p.r + v1)) / p.r := by
      apply div_le_div_of_nonneg_right _ hr.le
      exact mul_le_mul_of_nonneg_left hlog hc.le
    have e2 : p.c * (1 + (Real.log (p.L * p.lam / (p.r + v1) / p.c) + Real.log ((p.r + v1) / p.r))) / p.r
        = p.c * (1 + Real.log (p.L * p.lam / (p.r + v1) / p.c)) / p.r
          + p.c * Real.log ((p.r + v1) / p.r) / p.r := by ring
    rw [e2]
    linarith
  -- small v
  have hhcont : ContinuousAt h 0 := by
    simp only [hhdef]
    refine continuousAt_const.sub (((mfun_continuous hc).continuousAt.comp ?_).div_const _)
    exact continuousAt_const.div (continuousAt_const.add continuousAt_id) (by simp; exact hr.ne')
  have hev : ∀ᶠ a in nhdsWithin (0:ℝ) (Ioi 0), h a < Grand p K v1 ∧ a ∈ Ioo 0 v1 :=
    ((hhcont.eventually (gt_mem_nhds hbeat)).filter_mono nhdsWithin_le_nhds).and
      (Ioo_mem_nhdsGT hv1)
  obtain ⟨a, ha1, ha2⟩ := hev.exists
  have hh_mono : ∀ x y, 0 ≤ x → x ≤ y → h x ≤ h y := by
    intro x y hx hxy
    simp only [hhdef]
    have : mfun p.c (p.L * p.lam / (p.r + y)) ≤ mfun p.c (p.L * p.lam / (p.r + x)) :=
      mfun_mono hc (div_le_div_of_nonneg_left hLl.le (by linarith) (by linarith))
    have := div_le_div_of_nonneg_right this hr.le
    linarith
  have hsmall : ∀ v, 0 < v → v ≤ a → Grand p K v ≤ Grand p K v1 := by
    intro v hv hva
    have : Grand p K v ≤ h v := by
      simp only [Grand, hhdef]; linarith [Kterm_nonneg p.r K hr hK.le hv]
    linarith [hh_mono v a hv.le hva]
  -- large v
  set M := mubar p / p.r - Grand p K v1 with hM
  set b := max p.r (3 * p.r * M / K + 1) with hbdef
  have hb : 0 < b := lt_max_of_lt_left hr
  have hlarge : ∀ v, b ≤ v → Grand p K v ≤ Grand p K v1 := by
    intro v hbv
    have hv : 0 < v := hb.trans_le hbv
    have hrv : p.r ≤ v := (le_max_left _ _).trans hbv
    have hy : 0 < p.r / v := div_pos hr hv
    have hy1 : p.r / v ≤ 1 := (div_le_one hv).2 hrv
    have h1 : Real.exp (p.r / v) - 1 ≤ 3 * (p.r / v) := by
      have a1 := Real.add_one_le_exp (-(p.r / v))
      have a2 : Real.exp (p.r / v) ≤ 3 := by
        have h1' := Real.exp_le_exp.2 hy1
        have h2' := Real.exp_one_lt_d9
        norm_num at h2'
        linarith
      have a3 : Real.exp (p.r / v) * Real.exp (-(p.r / v)) = 1 := by
        rw [← Real.exp_add]; simp
      nlinarith [Real.exp_pos (p.r / v)]
    have hpos : 0 < Real.exp (p.r / v) - 1 := by
      have := Real.add_one_lt_exp hy.ne'; linarith
    have hKv : K * v / (3 * p.r) ≤ K / (Real.exp (p.r / v) - 1) := by
      rw [div_le_div_iff₀ (by positivity) hpos]
      have e : K * v * (3 * (p.r / v)) = K * (3 * p.r) := by field_simp
      linarith [mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ K * v)]
    have hMv : M < K * v / (3 * p.r) := by
      have : 3 * p.r * M / K + 1 ≤ v := (le_max_right _ _).trans hbv
      rw [lt_div_iff₀ (by positivity)]
      rw [div_add_one hK.ne', div_le_iff₀ hK] at this
      nlinarith
    have hm0 : 0 ≤ mfun p.c (p.L * p.lam / (p.r + v)) := by
      have := mfun_le hc (div_pos hLl (add_pos hr hv)) (le_refl 0)
      have h' : 0 ≤ mfun p.c (p.L * p.lam / (p.r + v)) ∨ True := Or.inr trivial
      unfold mfun; split_ifs with hh
      · have : 1 ≤ p.L * p.lam / (p.r + v) / p.c := by rw [le_div_iff₀ hc]; linarith
        have := Real.log_nonneg this
        positivity
      · exact (div_pos hLl (add_pos hr hv)).le
    simp only [Grand] at hM ⊢
    have := div_nonneg hm0 hr.le
    linarith
  -- compactness on [a, b]
  have hab : a ≤ b := by
    have : a < v1 := ha2.2
    linarith [hv1r, le_max_left p.r (3 * p.r * M / K + 1)]
  obtain ⟨vs, hvs, hmax⟩ := (isCompact_Icc (a := a) (b := b)).exists_isMaxOn
    (nonempty_Icc.2 hab) ((Grand_continuousOn p hp K).mono fun x hx => ha2.1.trans_le hx.1)
  have hv1mem : v1 ∈ Icc a b := ⟨ha2.2.le, hv1r.trans (le_max_left _ _)⟩
  refine ⟨vs, ha2.1.trans_le hvs.1, fun v hv => ?_⟩
  have h1 : Grand p K v1 ≤ Grand p K vs := hmax hv1mem
  by_cases hva : v ≤ a
  · exact (hsmall v hv hva).trans h1
  · by_cases hvb : b ≤ v
    · exact (hlarge v hvb).trans h1
    · exact hmax ⟨(not_le.1 hva).le, (not_le.1 hvb).le⟩
/-! ### The hybrid law -/

lemma hyb_meas_shift (d : ℝ) : Measurable fun t : ℝ => t + d := measurable_id.add_const d

lemma hyb_prob {q v : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hv : 0 < v) :
    IsProbabilityMeasure (hybridLaw q v) := by
  have := ProbabilityTheory.isProbabilityMeasure_expMeasure hv
  constructor
  rw [hybridLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply (hyb_meas_shift _) MeasurableSet.univ, preimage_univ, measure_univ,
    measure_univ, smul_eq_mul, smul_eq_mul, mul_one, mul_one,
    ← ENNReal.ofReal_add hq0 (by linarith)]
  simp

lemma hyb_Iio {q v : ℝ} (hv : 0 < v) : hybridLaw q v (Iio (q / v)) = 0 := by
  rw [hybridLaw, Measure.add_apply, Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply (hyb_meas_shift _) measurableSet_Iio,
    Measure.dirac_apply' _ measurableSet_Iio]
  have h2 : (fun t => t + q / v) ⁻¹' Iio (q / v) = Iio 0 := by ext t; simp
  rw [h2, measure_mono_null Iio_subset_Iic_self (expMeasure_Iic_zero hv)]
  simp

lemma hyb_ae_ge {q v : ℝ} (hv : 0 < v) : ∀ᵐ τ ∂(hybridLaw q v), q / v ≤ τ := by
  rw [ae_iff]
  have : {a : ℝ | ¬ q / v ≤ a} = Iio (q / v) := by ext a; simp
  rw [this]; exact hyb_Iio hv

lemma hyb_Iic_zero {q v : ℝ} (hq : 0 < q) (hv : 0 < v) : hybridLaw q v (Iic 0) = 0 :=
  measure_mono_null (Iic_subset_Iio.2 (div_pos hq hv)) (hyb_Iio hv)

lemma expTail {v : ℝ} (hv : 0 < v) {s : ℝ} (hs : 0 ≤ s) :
    ProbabilityTheory.expMeasure v (Ioi s) = ENNReal.ofReal (Real.exp (-(v * s))) := by
  have := ProbabilityTheory.isProbabilityMeasure_expMeasure hv
  have h := ProbabilityTheory.cdf_expMeasure_eq hv s
  rw [ProbabilityTheory.cdf_eq_real, if_pos hs] at h
  rw [← ofReal_measureReal, ← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ, h]
  congr 1; ring

lemma Sv_hyb_lt {q v : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hv : 0 < v) {t : ℝ} (ht : t < q / v) :
    Sv (hybridLaw q v) t = 1 := by
  have := hyb_prob hq0 hq1 hv
  rw [Sv, setIntegral_const, smul_eq_mul, mul_one, ← compl_Iic,
    measureReal_compl measurableSet_Iic, probReal_univ]
  have h0 : (hybridLaw q v).real (Iic t) = 0 := by
    rw [measureReal_eq_zero_iff]; exact measure_mono_null (Iic_subset_Iio.2 ht) (hyb_Iio hv)
  rw [h0]; ring

lemma Sv_hyb_ge {q v : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hv : 0 < v) {t : ℝ} (ht : q / v ≤ t) :
    Sv (hybridLaw q v) t = (1 - q) * Real.exp (-(v * (t - q / v))) := by
  rw [Sv, setIntegral_const, smul_eq_mul, mul_one, Measure.real, hybridLaw, Measure.add_apply,
    Measure.smul_apply, Measure.smul_apply,
    Measure.map_apply (hyb_meas_shift _) measurableSet_Ioi,
    Measure.dirac_apply' _ measurableSet_Ioi]
  have h2 : (fun x => x + q / v) ⁻¹' Ioi t = Ioi (t - q / v) := by
    ext x; simp only [mem_preimage, mem_Ioi]; constructor <;> intro h <;> linarith
  have h1 : (Ioi t).indicator (1 : ℝ → ℝ≥0∞) (q / v) = 0 :=
    indicator_of_notMem (show q / v ∉ Ioi t from not_lt.2 ht) _
  rw [h2, h1, expTail hv (by linarith), smul_eq_mul, smul_eq_mul, mul_zero, zero_add,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith),
    ENNReal.toReal_ofReal (Real.exp_pos _).le]

lemma integral_hyb {q v : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hv : 0 < v) (g : ℝ → ℝ)
    (hg : Measurable g)
    (hgi : Integrable (fun τ => g (τ + q / v)) (ProbabilityTheory.expMeasure v)) :
    ∫ τ, g τ ∂(hybridLaw q v) =
      q * g (q / v) + (1 - q) * ∫ τ, g (τ + q / v) ∂(ProbabilityTheory.expMeasure v) := by
  have hm : Integrable g ((ProbabilityTheory.expMeasure v).map (fun t => t + q / v)) :=
    (integrable_map_measure hg.aestronglyMeasurable (hyb_meas_shift _).aemeasurable).2 hgi
  rw [hybridLaw, integral_add_measure ((integrable_dirac (by simp)).smul_measure (by simp))
      (hm.smul_measure (by simp)), integral_smul_measure, integral_smul_measure, integral_dirac,
    integral_map (hyb_meas_shift _).aemeasurable hg.aestronglyMeasurable,
    ENNReal.toReal_ofReal hq0, ENNReal.toReal_ofReal (by linarith), smul_eq_mul, smul_eq_mul]

lemma ae_pos_exp {v : ℝ} (hv : 0 < v) : ∀ᵐ τ ∂(ProbabilityTheory.expMeasure v), 0 < τ := by
  rw [ae_iff]
  have : {a : ℝ | ¬ 0 < a} = Iic 0 := by ext a; simp
  rw [this]; exact expMeasure_Iic_zero hv

lemma discF_hyb (p : Params) (hp : Standing p) {q v : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hv : 0 < v) :
    discF p (hybridLaw q v) =
      Real.exp (-(p.r * (q / v))) * (q + (1 - q) * (v / (p.r + v))) := by
  have := ProbabilityTheory.isProbabilityMeasure_expMeasure hv
  have hi : Integrable (fun τ => Real.exp (-(p.r * (τ + q / v))))
      (ProbabilityTheory.expMeasure v) := by
    refine Integrable.of_bound
      ((measurable_exp_neg_r p.r).comp (hyb_meas_shift (q / v))).aestronglyMeasurable
      (Real.exp (-(p.r * (q / v)))) ((ae_pos_exp hv).mono fun τ hτ => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (by nlinarith [hp.hr])
  rw [discF, integral_hyb hq0 hq1 hv _ (measurable_exp_neg_r _) hi]
  have e : ∫ τ, Real.exp (-(p.r * (τ + q / v))) ∂(ProbabilityTheory.expMeasure v) =
      Real.exp (-(p.r * (q / v))) * discF p (randomLaw v) := by
    rw [discF, randomLaw, ← integral_const_mul]; congr 1; funext τ
    rw [← Real.exp_add]; ring_nf
  rw [e, discF_random p hp hv]; ring

lemma Qv_hyb_lt (p : Params) {q v : ℝ} (hv : 0 < v) {t : ℝ} (ht : t < q / v) :
    Qv p (hybridLaw q v) t = discF p (hybridLaw q v) := by
  rw [Qv, discF, Measure.restrict_eq_self_of_ae_mem ((hyb_ae_ge hv).mono fun τ hτ => ?_)]
  exact show t < τ from lt_of_lt_of_le ht hτ

lemma Qv_hyb_ge (p : Params) (hp : Standing p) {q v : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hv : 0 < v) {t : ℝ} (ht : q / v ≤ t) :
    Qv p (hybridLaw q v) t = (1 - q) * Real.exp (-(p.r * (q / v))) *
      (v / (p.r + v) * Real.exp (-((p.r + v) * (t - q / v)))) := by
  have := ProbabilityTheory.isProbabilityMeasure_expMeasure hv
  have hd : 0 ≤ t - q / v := by linarith
  have hgm : Measurable ((Ioi t).indicator fun τ => Real.exp (-(p.r * τ))) :=
    (measurable_exp_neg_r _).indicator measurableSet_Ioi
  have hshift : (fun τ => (Ioi t).indicator (fun τ => Real.exp (-(p.r * τ))) (τ + q / v)) =
      fun τ => Real.exp (-(p.r * (q / v))) *
        (Ioi (t - q / v)).indicator (fun τ => Real.exp (-(p.r * τ))) τ := by
    funext τ
    by_cases h : t - q / v < τ
    · rw [indicator_of_mem (show τ + q / v ∈ Ioi t from by simp only [mem_Ioi]; linarith),
        indicator_of_mem (show τ ∈ Ioi (t - q / v) from h), ← Real.exp_add]; ring_nf
    · rw [indicator_of_notMem (show τ + q / v ∉ Ioi t from by simp only [mem_Ioi]; linarith),
        indicator_of_notMem (show τ ∉ Ioi (t - q / v) from h), mul_zero]
  have hi : Integrable (fun τ => (Ioi t).indicator (fun τ => Real.exp (-(p.r * τ))) (τ + q / v))
      (ProbabilityTheory.expMeasure v) := by
    rw [hshift]
    exact ((integrableOn_exp_neg_r _ hp.hr (t - q / v)).integrable_indicator
      measurableSet_Ioi).const_mul _
  rw [Qv, ← integral_indicator measurableSet_Ioi, integral_hyb hq0 hq1 hv _ hgm hi, hshift,
    integral_const_mul, integral_indicator measurableSet_Ioi]
  have h0 : (Ioi t).indicator (fun τ => Real.exp (-(p.r * τ))) (q / v) = 0 :=
    indicator_of_notMem (show q / v ∉ Ioi t from not_lt.2 ht) _
  have hQ := Qv_random p hp hv hd
  rw [Qv, randomLaw] at hQ
  rw [h0, hQ]; ring

lemma integral_exp_lin (ρ a b : ℝ) (hρ : ρ ≠ 0) :
    ∫ t in a..b, Real.exp (-(ρ * t)) = (Real.exp (-(ρ * a)) - Real.exp (-(ρ * b))) / ρ := by
  have e : (fun t => Real.exp (-(ρ * t))) = fun t => Real.exp ((-ρ) * t) := by
    funext t; ring_nf
  rw [e, intervalIntegral.integral_comp_mul_left (f := Real.exp) (neg_ne_zero.2 hρ), integral_exp,
    smul_eq_mul, neg_mul, neg_mul, div_eq_mul_inv, inv_neg]
  ring

lemma Wv_hyb_ge (p : Params) (hp : Standing p) {q v : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hv : 0 < v) {s : ℝ} (hs0 : 0 ≤ s) (hs : q / v ≤ s) :
    Wv p (hybridLaw q v) s =
      (1 - q) * Real.exp (v * (q / v)) * (Real.exp (-((p.r + v) * s)) / (p.r + v)) := by
  have hρ : 0 < p.r + v := add_pos hp.hr hv
  rw [Wv, Measure.restrict_restrict measurableSet_Ioi, Ioi_inter_Ioi,
    show s ⊔ 0 = s from max_eq_left hs0, ← integral_exp_neg_Ioi_mul hρ, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [Sv_hyb_ge hq0 hq1 hv (hs.trans (le_of_lt ht))]
  rw [show Real.exp (-(p.r * t)) * ((1 - q) * Real.exp (-(v * (t - q / v)))) =
    (1 - q) * (Real.exp (-(p.r * t)) * Real.exp (-(v * (t - q / v)))) by ring,
    ← Real.exp_add, mul_assoc, ← Real.exp_add]
  ring_nf

lemma Wv_hyb_lt (p : Params) (hp : Standing p) {q v : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hv : 0 < v) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < q / v) :
    Wv p (hybridLaw q v) s = (Real.exp (-(p.r * s)) - Real.exp (-(p.r * (q / v)))) / p.r +
      Wv p (hybridLaw q v) (q / v) := by
  have := hyb_prob hq0 hq1 hv
  have hd0 : 0 ≤ q / v := hs0.trans hs.le
  have hint : IntegrableOn (fun t => Real.exp (-(p.r * t)) * Sv (hybridLaw q v) t) (Ioi s) := by
    refine Integrable.mono' ((integrableOn_exp_neg_Ioi_zero hp.hr).mono_set (Ioi_subset_Ioi hs0))
      ((measurable_exp_neg_r _).mul (Sv_anti _).measurable).aestronglyMeasurable
      (Filter.Eventually.of_forall fun t => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (Sv_nonneg _ t))]
    exact mul_le_of_le_one_right (Real.exp_pos _).le (Sv_le_one _ t)
  rw [Wv, Wv, Measure.restrict_restrict measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
    Ioi_inter_Ioi, Ioi_inter_Ioi, show s ⊔ 0 = s from max_eq_left hs0,
    show q / v ⊔ 0 = q / v from max_eq_left hd0,
    ← Ioc_union_Ioi_eq_Ioi hs.le, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hs.le))]
  congr 1
  rw [integral_Ioc_eq_integral_Ioo,
    setIntegral_congr_fun measurableSet_Ioo (g := fun t => Real.exp (-(p.r * t)))
      (fun t ht => by rw [Sv_hyb_lt hq0 hq1 hv ht.2, mul_one]),
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hs.le,
    integral_exp_lin _ _ _ hp.hr.ne']

lemma integral_exp_zero_lin (ρ b : ℝ) (hρ : ρ ≠ 0) :
    ∫ t in (0:ℝ)..b, Real.exp (-(ρ * t)) = (1 - Real.exp (-(ρ * b))) / ρ := by
  rw [integral_exp_lin ρ 0 b hρ]; simp

lemma integral_t_exp (ρ b : ℝ) (hρ : 0 < ρ) :
    ∫ t in (0:ℝ)..b, t * Real.exp (-(ρ * t)) =
      (1 - Real.exp (-(ρ * b)) * (1 + ρ * b)) / ρ ^ 2 := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t => -1 * (t / ρ + 1 / ρ ^ 2) * Real.exp (-(ρ * t)))
      (t * Real.exp (-(ρ * t))) t := by
    intro t
    have h1 : HasDerivAt (fun t => -(ρ * t)) (-ρ) t := by
      simpa using (hasDerivAt_id t).const_mul (-ρ)
    have h2 : HasDerivAt (fun t : ℝ => -1 * (t / ρ + 1 / ρ ^ 2)) (-1 * (1 / ρ)) t :=
      (((hasDerivAt_id' t).div_const ρ).add_const (1 / ρ ^ 2)).const_mul (-1)
    refine (h2.mul h1.exp).congr_deriv ?_
    field_simp <;> ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    ((by fun_prop : Continuous fun t : ℝ => t * Real.exp (-(ρ * t))).intervalIntegrable 0 b)]
  simp only [mul_zero, neg_zero, Real.exp_zero, zero_div, zero_add, mul_one]
  field_simp <;> ring

/-- Splitting an integral over `(0, ∞)` at `d`. -/
lemma split_Ioi {d : ℝ} (hd : 0 < d) (h g1 g2 : ℝ → ℝ)
    (h1 : ∀ t ∈ Ioo 0 d, h t = g1 t) (h2 : ∀ t ∈ Ioi d, h t = g2 t)
    (hg1 : Continuous g1) (hg2 : IntegrableOn g2 (Ioi d)) :
    IntegrableOn h (Ioi 0) ∧
      ∫ t in Ioi 0, h t = (∫ t in (0:ℝ)..d, g1 t) + ∫ t in Ioi d, g2 t := by
  have i1 : IntegrableOn h (Ioc 0 d) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact (hg1.integrableOn_Icc.mono_set Ioo_subset_Icc_self).congr_fun
      (fun t ht => (h1 t ht).symm) measurableSet_Ioo
  have i2 : IntegrableOn h (Ioi d) := hg2.congr_fun (fun t ht => (h2 t ht).symm) measurableSet_Ioi
  rw [← Ioc_union_Ioi_eq_Ioi hd.le]
  refine ⟨i1.union i2, ?_⟩
  rw [setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi i1 i2,
    integral_Ioc_eq_integral_Ioo, setIntegral_congr_fun measurableSet_Ioo h1,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hd.le,
    setIntegral_congr_fun measurableSet_Ioi h2]

lemma exp_upper4 {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + 5 * x ^ 4 / 96 := by
  have h := Real.exp_bound (x := x) (by rw [abs_of_nonneg hx0]; exact hx1) (n := 4) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, abs_of_nonneg hx0] at h
  norm_num at h
  have := (abs_le.1 h).2
  nlinarith

lemma log_upper {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.log (1 + x) ≤ x - x ^ 2 / 2 + 2 * x ^ 3 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := -x) (by rw [abs_neg, abs_of_nonneg hx0]; linarith)
    (n := 2)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, abs_of_nonneg hx0,
    sub_neg_eq_add] at h
  norm_num at h
  have h2 := (abs_le.1 h).2
  have h3 : x ^ 3 / (1 - x) ≤ 2 * x ^ 3 := by
    rw [div_le_iff₀ (by linarith)]; nlinarith [pow_nonneg hx0 3]
  linarith

/-- The core second-order inequality behind the effort regime. -/
lemma psi_core (x β ℓ e : ℝ) (hx0 : 0 < x) (hx1 : x ≤ 1 / 2) (hβ : 0 < β) (hxβ : x ≤ β / 8)
    (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ x - x ^ 2 / 2 + 2 * x ^ 3) (he0 : x ≤ e)
    (he1 : e ≤ x + x ^ 2 / 2 + x ^ 3 / 6 + 5 * x ^ 4 / 96) :
    ℓ * (1 + x) * e - x * (1 + x) * (1 + e) + (1 + β) * e ^ 2 / 2 + (1 - β * x) * e < 0 := by
  have x2 : x ^ 2 ≤ x / 2 := by nlinarith
  have x3 : x ^ 3 ≤ x / 4 := by
    have : x ^ 3 = x * x ^ 2 := by ring
    nlinarith
  have x4 : x ^ 4 ≤ x / 8 := by
    have : x ^ 4 = x * x ^ 3 := by ring
    nlinarith
  have p2 : x ^ 2 ≤ 1 / 4 := by nlinarith
  have p3 : x ^ 3 ≤ 1 / 8 := by nlinarith
  have p4 : x ^ 4 ≤ 1 / 16 := by nlinarith
  have p5 : x ^ 5 ≤ 1 / 32 := by
    have : x ^ 5 = x * x ^ 4 := by ring
    nlinarith [pow_pos hx0 4]
  have h1 : ℓ * (1 + x) * e ≤ (x - x ^ 2 / 2 + 2 * x ^ 3) * (1 + x) * e :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hℓ (by linarith)) (by linarith)
  set em := x + x ^ 2 / 2 + x ^ 3 / 6 + 5 * x ^ 4 / 96 with hem
  have hemx : x ≤ em := le_trans he0 he1
  have hb1 : e ^ 2 / 2 - x * e ≤ em ^ 2 / 2 - x * em := by
    nlinarith [mul_nonneg (sub_nonneg.2 he1) (show 0 ≤ em + e - 2 * x by linarith)]
  have hb2 : em / 2 - x ≤ -(7 / 20) * x := by rw [hem]; linarith
  have hb3 : em ^ 2 / 2 - x * em ≤ -(7 / 20) * x ^ 2 := by
    have e1 : em ^ 2 / 2 - x * em = em * (em / 2 - x) := by ring
    have e2 := mul_le_mul_of_nonneg_left hb2 (show 0 ≤ em by linarith)
    have e3 : 0 ≤ (em - x) * ((7 / 20) * x) := mul_nonneg (by linarith) (by linarith)
    rw [e1]; nlinarith
  set br := (x - x ^ 2 / 2 + 2 * x ^ 3) * (1 + x) - x * (1 + x) + 1 with hbr
  have hbr0 : 0 ≤ br := by
    have : br = 1 - x ^ 2 / 2 + (3 / 2) * x ^ 3 + 2 * x ^ 4 := by rw [hbr]; ring
    rw [this]; nlinarith [pow_pos hx0 3, pow_pos hx0 4]
  have hG : e * br - x * (1 + x) + e ^ 2 / 2 ≤ em * br - x * (1 + x) + em ^ 2 / 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 he1) (show 0 ≤ br + (em + e) / 2 by linarith)]
  have hP : -11 / 6 + 51 / 32 * x + 269 / 96 * x ^ 2 + 91 / 72 * x ^ 3 + 121 / 288 * x ^ 4 +
      1945 / 18432 * x ^ 5 ≤ 0 := by linarith
  have hGm : em * br - x * (1 + x) + em ^ 2 / 2 ≤ 2 * x ^ 3 := by
    have e1 : em * br - x * (1 + x) + em ^ 2 / 2 = 2 * x ^ 3 + x ^ 3 * (-11 / 6 + 51 / 32 * x +
        269 / 96 * x ^ 2 + 91 / 72 * x ^ 3 + 121 / 288 * x ^ 4 + 1945 / 18432 * x ^ 5) := by
      rw [hem, hbr]; ring
    rw [e1]
    have := mul_nonpos_of_nonneg_of_nonpos (pow_pos hx0 3).le hP
    linarith
  have hβ' : β * (e ^ 2 / 2 - x * e) ≤ β * (-(7 / 20) * x ^ 2) :=
    mul_le_mul_of_nonneg_left (hb1.trans hb3) hβ.le
  have hfin : 2 * x ^ 3 + β * (-(7 / 20) * x ^ 2) < 0 := by
    have h7 : 2 * x - 7 / 20 * β < 0 := by linarith
    have := mul_neg_of_pos_of_neg (pow_pos hx0 2) h7
    have e1 : 2 * x ^ 3 + β * (-(7 / 20) * x ^ 2) = x ^ 2 * (2 * x - 7 / 20 * β) := by ring
    rw [e1]; exact this
  have e2 : (x - x ^ 2 / 2 + 2 * x ^ 3) * (1 + x) * e - x * (1 + x) * (1 + e) +
      (1 + β) * e ^ 2 / 2 + (1 - β * x) * e =
      (e * br - x * (1 + x) + e ^ 2 / 2) + β * (e ^ 2 / 2 - x * e) := by rw [hbr]; ring
  linarith

/-- Zero-effort criterion `e^x < 1 + x + x²`. -/
lemma exp_lt_quad {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1 / 2) : Real.exp x < 1 + x + x ^ 2 := by
  have := exp_upper4 hx0.le (by linarith)
  nlinarith [pow_pos hx0 2, pow_pos hx0 3, pow_pos hx0 4]

/-! ### The effort regime: implemented effort and its costs -/

/-- Agent effort under the hybrid law with penalty `L / v`. -/
noncomputable def aH (r κ x d : ℝ) (t : ℝ) : ℝ :=
  if t < d then Real.log (1 + x) - Real.log κ - r * (d - max t 0) else -Real.log κ

lemma aH_lt {r κ x d t : ℝ} (ht0 : 0 ≤ t) (ht : t < d) :
    aH r κ x d t = Real.log (1 + x) - Real.log κ - r * (d - t) := by
  rw [aH, if_pos ht, max_eq_left ht0]

lemma aH_ge {r κ x d t : ℝ} (ht : d ≤ t) : aH r κ x d t = -Real.log κ := by
  rw [aH, if_neg (not_lt.2 ht)]

lemma exp_neg_aH_lt {r κ x d t : ℝ} (hκ : 0 < κ) (hx : 0 < 1 + x) (ht0 : 0 ≤ t) (ht : t < d) :
    Real.exp (-(aH r κ x d t)) = κ / (1 + x) * Real.exp (r * d) * Real.exp (-(r * t)) := by
  rw [aH_lt ht0 ht, show -(Real.log (1 + x) - Real.log κ - r * (d - t)) =
    (Real.log κ + r * d + -(r * t)) - Real.log (1 + x) by ring, Real.exp_sub, Real.exp_add,
    Real.exp_add, Real.exp_log hκ, Real.exp_log hx]
  ring

lemma aH_admissible {r κ x d : ℝ} (hr : 0 < r) (hd : 0 < d) (hxd : x = r * d) (hκ : 0 < κ)
    (hκ1 : κ ≤ 1) (hadm : κ * Real.exp x ≤ 1 + x) : Admissible (aH r κ x d) := by
  have hx : 0 < 1 + x := by rw [hxd]; nlinarith
  have hlog : x ≤ Real.log (1 + x) - Real.log κ := by
    rw [← Real.log_div hx.ne' hκ.ne', Real.le_log_iff_exp_le (div_pos hx hκ), le_div_iff₀ hκ]
    linarith [mul_comm κ (Real.exp x)]
  have hlk : 0 ≤ -Real.log κ := neg_nonneg.2 (Real.log_nonpos hκ.le hκ1)
  refine ⟨?_, fun t => ?_, Real.log (1 + x) - Real.log κ, fun t => ?_⟩
  · exact Measurable.ite measurableSet_Iio (by fun_prop) measurable_const
  · unfold aH
    split_ifs with h
    · have : r * (d - max t 0) ≤ x := by
        rw [hxd]; nlinarith [le_max_right t 0]
      linarith
    · exact hlk
  · unfold aH
    split_ifs with h
    · have : 0 ≤ r * (d - max t 0) := mul_nonneg hr.le (by
        rcases le_total t 0 with h0 | h0
        · rw [max_eq_right h0]; linarith
        · rw [max_eq_left h0]; linarith)
      linarith
    · have hx0 : 0 ≤ x := by rw [hxd]; positivity
      have := Real.log_nonneg (show (1:ℝ) ≤ 1 + x by linarith)
      linarith

lemma intOn_exp_Ioi {ρ : ℝ} (hρ : 0 < ρ) (d : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (-(ρ * t))) (Ioi d) := by
  simpa [neg_mul] using integrableOn_exp_mul_Ioi (neg_neg_of_pos hρ) d

lemma effortH_val (p : Params) (hp : Standing p) {q v κ : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hv : 0 < v) :
    ∫ t in Ioi 0, aH p.r κ (p.r * (q / v)) (q / v) t * Real.exp (-(p.r * t)) *
        Sv (hybridLaw q v) t =
      (Real.log (1 + p.r * (q / v)) - Real.log κ - p.r * (q / v)) *
          ((1 - Real.exp (-(p.r * (q / v)))) / p.r) +
        p.r * ((1 - Real.exp (-(p.r * (q / v))) * (1 + p.r * (q / v))) / p.r ^ 2) +
      -Real.log κ * (1 - q) * Real.exp (v * (q / v)) *
        (Real.exp (-((p.r + v) * (q / v))) / (p.r + v)) := by
  have hd : 0 < q / v := div_pos hq0 hv
  have hρ : 0 < p.r + v := add_pos hp.hr hv
  have h1 : ∀ t ∈ Ioo 0 (q / v), aH p.r κ (p.r * (q / v)) (q / v) t * Real.exp (-(p.r * t)) *
      Sv (hybridLaw q v) t = (Real.log (1 + p.r * (q / v)) - Real.log κ - p.r * (q / v)) *
      Real.exp (-(p.r * t)) + p.r * (t * Real.exp (-(p.r * t))) := by
    intro t ht
    rw [aH_lt ht.1.le ht.2, Sv_hyb_lt hq0.le hq1 hv ht.2]; ring
  have h2 : ∀ t ∈ Ioi (q / v), aH p.r κ (p.r * (q / v)) (q / v) t * Real.exp (-(p.r * t)) *
      Sv (hybridLaw q v) t =
      -Real.log κ * (1 - q) * Real.exp (v * (q / v)) * Real.exp (-((p.r + v) * t)) := by
    intro t ht
    have ht' : q / v ≤ t := le_of_lt ht
    rw [aH_ge ht', Sv_hyb_ge hq0.le hq1 hv ht']
    have e : Real.exp (-(p.r * t)) * Real.exp (-(v * (t - q / v))) =
        Real.exp (v * (q / v)) * Real.exp (-((p.r + v) * t)) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    linear_combination (-Real.log κ * (1 - q)) * e
  obtain ⟨_, hsplit⟩ := split_Ioi hd
    (fun t => aH p.r κ (p.r * (q / v)) (q / v) t * Real.exp (-(p.r * t)) * Sv (hybridLaw q v) t)
    (fun t => (Real.log (1 + p.r * (q / v)) - Real.log κ - p.r * (q / v)) *
      Real.exp (-(p.r * t)) + p.r * (t * Real.exp (-(p.r * t))))
    (fun t => -Real.log κ * (1 - q) * Real.exp (v * (q / v)) * Real.exp (-((p.r + v) * t)))
    h1 h2 (by fun_prop) ((intOn_exp_Ioi hρ _).const_mul _)
  rw [hsplit, intervalIntegral.integral_add ((by fun_prop : Continuous fun t =>
      (Real.log (1 + p.r * (q / v)) - Real.log κ - p.r * (q / v)) *
        Real.exp (-(p.r * t))).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t => p.r * (t * Real.exp (-(p.r * t)))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_exp_zero_lin _ _ hp.hr.ne', integral_t_exp _ _ hp.hr, integral_const_mul,
    integral_exp_neg_Ioi_mul hρ]

lemma lossH_val (p : Params) (hp : Standing p) {q v κ : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hv : 0 < v) (hκ : 0 < κ) :
    ∫ t in Ioi 0, Real.exp (-(aH p.r κ (p.r * (q / v)) (q / v) t)) * Wv p (hybridLaw q v) t =
      κ / (1 + p.r * (q / v)) * Real.exp (p.r * (q / v)) *
        (1 / p.r * ((1 - Real.exp (-((2 * p.r) * (q / v)))) / (2 * p.r)) +
          ((1 - q) * Real.exp (v * (q / v)) * (Real.exp (-((p.r + v) * (q / v))) / (p.r + v)) -
            Real.exp (-(p.r * (q / v))) / p.r) * ((1 - Real.exp (-(p.r * (q / v)))) / p.r)) +
      κ * ((1 - q) * Real.exp (v * (q / v)) / (p.r + v)) *
        (Real.exp (-((p.r + v) * (q / v))) / (p.r + v)) := by
  have hd : 0 < q / v := div_pos hq0 hv
  have hρ : 0 < p.r + v := add_pos hp.hr hv
  have hx : 0 < 1 + p.r * (q / v) := by nlinarith [hp.hr]
  have h2r : (0:ℝ) < 2 * p.r := by linarith [hp.hr]
  set Wd := (1 - q) * Real.exp (v * (q / v)) * (Real.exp (-((p.r + v) * (q / v))) / (p.r + v))
    with hWd
  have h1 : ∀ t ∈ Ioo 0 (q / v), Real.exp (-(aH p.r κ (p.r * (q / v)) (q / v) t)) *
      Wv p (hybridLaw q v) t = κ / (1 + p.r * (q / v)) * Real.exp (p.r * (q / v)) *
      (1 / p.r * Real.exp (-((2 * p.r) * t)) + (Wd - Real.exp (-(p.r * (q / v))) / p.r) *
        Real.exp (-(p.r * t))) := by
    intro t ht
    rw [exp_neg_aH_lt hκ hx ht.1.le ht.2, Wv_hyb_lt p hp hq0.le hq1 hv ht.1.le ht.2,
      Wv_hyb_ge p hp hq0.le hq1 hv hd.le le_rfl, ← hWd]
    have e : Real.exp (-(p.r * t)) * Real.exp (-(p.r * t)) = Real.exp (-((2 * p.r) * t)) := by
      rw [← Real.exp_add]; ring_nf
    rw [← e]; ring
  have h2 : ∀ t ∈ Ioi (q / v), Real.exp (-(aH p.r κ (p.r * (q / v)) (q / v) t)) *
      Wv p (hybridLaw q v) t =
      κ * ((1 - q) * Real.exp (v * (q / v)) / (p.r + v)) * Real.exp (-((p.r + v) * t)) := by
    intro t ht
    have ht' : q / v ≤ t := le_of_lt ht
    rw [aH_ge ht', neg_neg, Real.exp_log hκ, Wv_hyb_ge p hp hq0.le hq1 hv (hd.le.trans ht') ht']
    ring
  obtain ⟨_, hsplit⟩ := split_Ioi hd
    (fun t => Real.exp (-(aH p.r κ (p.r * (q / v)) (q / v) t)) * Wv p (hybridLaw q v) t)
    (fun t => κ / (1 + p.r * (q / v)) * Real.exp (p.r * (q / v)) *
      (1 / p.r * Real.exp (-((2 * p.r) * t)) + (Wd - Real.exp (-(p.r * (q / v))) / p.r) *
        Real.exp (-(p.r * t))))
    (fun t => κ * ((1 - q) * Real.exp (v * (q / v)) / (p.r + v)) * Real.exp (-((p.r + v) * t)))
    h1 h2 (by fun_prop) ((intOn_exp_Ioi hρ _).const_mul _)
  rw [hsplit, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add ((by fun_prop : Continuous fun t =>
      1 / p.r * Real.exp (-((2 * p.r) * t))).intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t => (Wd - Real.exp (-(p.r * (q / v))) / p.r) *
      Real.exp (-(p.r * t))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_exp_zero_lin _ _ h2r.ne', integral_exp_zero_lin _ _ hp.hr.ne', integral_const_mul,
    integral_exp_neg_Ioi_mul hρ]

lemma lossZ_val (p : Params) (hp : Standing p) {q v : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hv : 0 < v) :
    ∫ t in Ioi 0, Wv p (hybridLaw q v) t =
      1 / p.r * ((1 - Real.exp (-(p.r * (q / v)))) / p.r) +
        (q / v) * ((1 - q) * Real.exp (v * (q / v)) * (Real.exp (-((p.r + v) * (q / v))) /
          (p.r + v)) - Real.exp (-(p.r * (q / v))) / p.r) +
      (1 - q) * Real.exp (v * (q / v)) / (p.r + v) *
        (Real.exp (-((p.r + v) * (q / v))) / (p.r + v)) := by
  have hd : 0 < q / v := div_pos hq0 hv
  have hρ : 0 < p.r + v := add_pos hp.hr hv
  set Wd := (1 - q) * Real.exp (v * (q / v)) * (Real.exp (-((p.r + v) * (q / v))) / (p.r + v))
    with hWd
  have h1 : ∀ t ∈ Ioo 0 (q / v), Wv p (hybridLaw q v) t =
      1 / p.r * Real.exp (-(p.r * t)) + (Wd - Real.exp (-(p.r * (q / v))) / p.r) := by
    intro t ht
    rw [Wv_hyb_lt p hp hq0.le hq1 hv ht.1.le ht.2, Wv_hyb_ge p hp hq0.le hq1 hv hd.le le_rfl,
      ← hWd]
    ring
  have h2 : ∀ t ∈ Ioi (q / v), Wv p (hybridLaw q v) t =
      (1 - q) * Real.exp (v * (q / v)) / (p.r + v) * Real.exp (-((p.r + v) * t)) := by
    intro t ht
    rw [Wv_hyb_ge p hp hq0.le hq1 hv (hd.le.trans (le_of_lt ht)) (le_of_lt ht)]
    ring
  obtain ⟨_, hsplit⟩ := split_Ioi hd (fun t => Wv p (hybridLaw q v) t)
    (fun t => 1 / p.r * Real.exp (-(p.r * t)) + (Wd - Real.exp (-(p.r * (q / v))) / p.r))
    (fun t => (1 - q) * Real.exp (v * (q / v)) / (p.r + v) * Real.exp (-((p.r + v) * t)))
    h1 h2 (by fun_prop) ((intOn_exp_Ioi hρ _).const_mul _)
  rw [hsplit, intervalIntegral.integral_add ((by fun_prop : Continuous fun t =>
      1 / p.r * Real.exp (-(p.r * t))).intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
    integral_exp_zero_lin _ _ hp.hr.ne', integral_const_mul, integral_exp_neg_Ioi_mul hρ,
    smul_eq_mul, sub_zero]

/-- The effort-regime identity `r T = (1 + A)(1 - δ) + Ψ`. -/
lemma effort_algebra (r v q κ : ℝ) (hr : 0 < r) (hv : 0 < v) (hκ : 0 < κ)
    (hx : 0 < 1 + r * (q / v)) :
    r * (((Real.log (1 + r * (q / v)) - Real.log κ - r * (q / v)) *
          ((1 - Real.exp (-(r * (q / v)))) / r) +
        r * ((1 - Real.exp (-(r * (q / v))) * (1 + r * (q / v))) / r ^ 2) +
        -Real.log κ * (1 - q) * Real.exp (v * (q / v)) *
          (Real.exp (-((r + v) * (q / v))) / (r + v))) +
      (r + v) / κ * (κ / (1 + r * (q / v)) * Real.exp (r * (q / v)) *
        (1 / r * ((1 - Real.exp (-((2 * r) * (q / v)))) / (2 * r)) +
          ((1 - q) * Real.exp (v * (q / v)) * (Real.exp (-((r + v) * (q / v))) / (r + v)) -
            Real.exp (-(r * (q / v))) / r) * ((1 - Real.exp (-(r * (q / v)))) / r)) +
      κ * ((1 - q) * Real.exp (v * (q / v)) / (r + v)) *
        (Real.exp (-((r + v) * (q / v))) / (r + v)))) =
    (1 + -Real.log κ) * (1 - Real.exp (-(r * (q / v))) * (q + (1 - q) * (v / (r + v)))) +
      (Real.log (1 + r * (q / v)) * (1 - Real.exp (-(r * (q / v)))) - r * (q / v) +
        (1 + v / r) * (((Real.exp (-(r * (q / v))))⁻¹ + Real.exp (-(r * (q / v)))) / 2 - 1) /
          (1 + r * (q / v)) +
        (1 - v / r * (r * (q / v))) * (1 - Real.exp (-(r * (q / v)))) / (1 + r * (q / v))) := by
  have hρ : 0 < r + v := add_pos hr hv
  have hE : Real.exp (r * (q / v)) = (Real.exp (-(r * (q / v))))⁻¹ := by
    rw [Real.exp_neg, inv_inv]
  have h2 : Real.exp (-((2 * r) * (q / v))) = Real.exp (-(r * (q / v))) ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  have h3 : Real.exp (-((r + v) * (q / v))) = Real.exp (-(r * (q / v))) / Real.exp (v * (q / v)) := by
    rw [← Real.exp_sub]; ring_nf
  have hw : Real.exp (v * (q / v)) ≠ 0 := (Real.exp_pos _).ne'
  have hu : Real.exp (-(r * (q / v))) ≠ 0 := (Real.exp_pos _).ne'
  rw [hE, h2, h3]
  field_simp
  ring

/-- `Ψ < 0` for a small hybrid. -/
lemma psi_neg (r v x : ℝ) (hr : 0 < r) (hv : 0 < v) (hx0 : 0 < x) (hx1 : x ≤ 1 / 2)
    (hxβ : x ≤ v / r / 8) :
    Real.log (1 + x) * (1 - Real.exp (-x)) - x +
        (1 + v / r) * (((Real.exp (-x))⁻¹ + Real.exp (-x)) / 2 - 1) / (1 + x) +
        (1 - v / r * x) * (1 - Real.exp (-x)) / (1 + x) < 0 := by
  have hβ : 0 < v / r := div_pos hv hr
  have hEx : (Real.exp (-x))⁻¹ = Real.exp x := by rw [Real.exp_neg, inv_inv]
  have hE0 : 0 < Real.exp x := Real.exp_pos x
  have hcore := psi_core x (v / r) (Real.log (1 + x)) (Real.exp x - 1) hx0 hx1 hβ hxβ
    (Real.log_nonneg (by linarith)) (log_upper hx0.le hx1)
    (by linarith [Real.add_one_le_exp x]) (by linarith [exp_upper4 hx0.le (by linarith)])
  have e : Real.log (1 + x) * (1 - Real.exp (-x)) - x +
        (1 + v / r) * (((Real.exp (-x))⁻¹ + Real.exp (-x)) / 2 - 1) / (1 + x) +
        (1 - v / r * x) * (1 - Real.exp (-x)) / (1 + x) =
      (Real.log (1 + x) * (1 + x) * (Real.exp x - 1) - x * (1 + x) * (1 + (Real.exp x - 1)) +
        (1 + v / r) * (Real.exp x - 1) ^ 2 / 2 + (1 - v / r * x) * (Real.exp x - 1)) /
        ((1 + x) * Real.exp x) := by
    rw [hEx, Real.exp_neg]
    field_simp
    ring
  rw [e]
  exact div_neg_of_neg_of_pos hcore (mul_pos (by linarith) hE0)

/-- The zero-effort identity `(1 - δ) - r (r + v) ∫ W = β u (1 + x + x² - e^x)`. -/
lemma zero_algebra (r v q : ℝ) (hr : 0 < r) (hv : 0 < v) :
    (1 - Real.exp (-(r * (q / v))) * (q + (1 - q) * (v / (r + v)))) -
      r * (r + v) * (1 / r * ((1 - Real.exp (-(r * (q / v)))) / r) +
        (q / v) * ((1 - q) * Real.exp (v * (q / v)) * (Real.exp (-((r + v) * (q / v))) /
          (r + v)) - Real.exp (-(r * (q / v))) / r) +
      (1 - q) * Real.exp (v * (q / v)) / (r + v) *
        (Real.exp (-((r + v) * (q / v))) / (r + v))) =
    v / r * Real.exp (-(r * (q / v))) *
      (1 + r * (q / v) + (r * (q / v)) ^ 2 - (Real.exp (-(r * (q / v))))⁻¹) := by
  have hρ : 0 < r + v := add_pos hr hv
  have h3 : Real.exp (-((r + v) * (q / v))) = Real.exp (-(r * (q / v))) / Real.exp (v * (q / v)) := by
    rw [← Real.exp_sub]; ring_nf
  have hw : Real.exp (v * (q / v)) ≠ 0 := (Real.exp_pos _).ne'
  have hu : Real.exp (-(r * (q / v))) ≠ 0 := (Real.exp_pos _).ne'
  rw [h3]
  field_simp
  ring

/-! ### C2c: a small hybrid beats `Grand v` -/

lemma pointwise_min {c α β a0 : ℝ} (hcα : 0 ≤ c * α) (hb : β * Real.exp (-a0) = c * α)
    (a : ℝ) : c * α * a0 + β * Real.exp (-a0) ≤ c * α * a + β * Real.exp (-a) := by
  have e : β * Real.exp (-a) = c * α * Real.exp (a0 - a) := by
    rw [← hb, mul_assoc, ← Real.exp_add]; ring_nf
  rw [e, hb]
  have := Real.add_one_le_exp (a0 - a)
  nlinarith

lemma Qv_nonneg (p : Params) (F : Measure ℝ) (t : ℝ) : 0 ≤ Qv p F t :=
  setIntegral_nonneg measurableSet_Ioi fun _ _ => (Real.exp_pos _).le

lemma Qv_anti (p : Params) (hp : Standing p) (F : Measure ℝ) [IsProbabilityMeasure F] :
    Antitone (Qv p F) := by
  intro s t hst
  exact setIntegral_mono_set (integrableOn_exp_neg_r F hp.hr s)
    (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
    (Filter.Eventually.of_forall (Ioi_subset_Ioi hst))

lemma Qv_le (p : Params) (hp : Standing p) (F : Measure ℝ) [IsProbabilityMeasure F] (t : ℝ) :
    Qv p F t ≤ Real.exp (-(p.r * t)) := by
  calc Qv p F t ≤ ∫ τ in Ioi t, Real.exp (-(p.r * t)) ∂F :=
        setIntegral_mono_on (integrableOn_exp_neg_r F hp.hr t) integrableOn_const
          measurableSet_Ioi fun τ hτ => Real.exp_le_exp.2 (by nlinarith [mem_Ioi.mp hτ, hp.hr])
    _ ≤ Real.exp (-(p.r * t)) := by
        rw [setIntegral_const, smul_eq_mul]
        exact mul_le_of_le_one_left (Real.exp_pos _).le measureReal_le_one

lemma intOn_bdd_S (p : Params) (hp : Standing p) (F : Measure ℝ) [IsProbabilityMeasure F]
    (g : ℝ → ℝ) (hg : Measurable g) (C : ℝ) (hC : ∀ t, |g t| ≤ C) :
    IntegrableOn (fun t => g t * Real.exp (-(p.r * t)) * Sv F t) (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_exp_neg_Ioi_zero hp.hr).const_mul C)
    ((hg.mul (measurable_exp_neg_r _)).mul (Sv_anti F).measurable).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
    abs_of_nonneg (Sv_nonneg F t)]
  have h1 := mul_le_mul_of_nonneg_right (hC t) (Real.exp_pos (-(p.r * t))).le
  have h2 : 0 ≤ |g t| * Real.exp (-(p.r * t)) := mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  nlinarith [Sv_le_one F t, Sv_nonneg F t]

lemma intOn_bdd_Q (p : Params) (hp : Standing p) (F : Measure ℝ) [IsProbabilityMeasure F]
    (g : ℝ → ℝ) (hg : Measurable g) (C : ℝ) (hC : ∀ t, |g t| ≤ C) :
    IntegrableOn (fun t => g t * Qv p F t) (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_exp_neg_Ioi_zero hp.hr).const_mul C)
    (hg.mul (Qv_anti p hp F).measurable).aestronglyMeasurable
    (Filter.Eventually.of_forall fun t => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Qv_nonneg p F t)]
  have h0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  calc |g t| * Qv p F t ≤ C * Qv p F t := mul_le_mul_of_nonneg_right (hC t) (Qv_nonneg p F t)
    _ ≤ C * Real.exp (-(p.r * t)) := mul_le_mul_of_nonneg_left (Qv_le p hp F t) h0

lemma admissible_bound {a : Effort} (ha : Admissible a) : ∃ C, ∀ t, |a t| ≤ C := by
  obtain ⟨_, h0, B, hB⟩ := ha
  exact ⟨B, fun t => by rw [abs_of_nonneg (h0 t)]; exact hB t⟩

lemma exp_neg_bound {a : Effort} (ha : Admissible a) : ∀ t, |Real.exp (-(a t))| ≤ 1 := by
  intro t
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.2 (neg_nonpos.2 (ha.2.1 t))

/-- The agent's cost as one integral. -/
lemma agentCost_eq (p : Params) (hp : Standing p) (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : F (Iic 0) = 0) (P : ℝ) (a : Effort) (ha : Admissible a) :
    p.c * effortInt p F a + P * penaltyInt p F a =
      ∫ t in Ioi 0, (p.c * (a t * Real.exp (-(p.r * t)) * Sv F t) +
        P * p.lam * (Real.exp (-(a t)) * Qv p F t)) := by
  obtain ⟨C, hC⟩ := admissible_bound ha
  rw [integral_add ((intOn_bdd_S p hp F a ha.1 C hC).const_mul _)
      ((intOn_bdd_Q p hp F _ (measurable_exp_neg_a a ha) 1 (exp_neg_bound ha)).const_mul _),
    integral_const_mul, integral_const_mul, effortInt_eq p F hF a ha, penaltyInt_eq p hp F hF a ha]
  ring

lemma agentOpt_of_pointwise (p : Params) (hp : Standing p) (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : F (Iic 0) = 0) (hδ : discF p F < 1) (P : ℝ) (a : Effort) (ha : Admissible a)
    (hpt : ∀ t, 0 < t → ∀ b : ℝ, 0 ≤ b →
      p.c * (a t * Real.exp (-(p.r * t)) * Sv F t) + P * p.lam * (Real.exp (-(a t)) * Qv p F t) ≤
      p.c * (b * Real.exp (-(p.r * t)) * Sv F t) + P * p.lam * (Real.exp (-b) * Qv p F t)) :
    AgentOptimal p F P a := by
  refine ⟨ha, fun a' ha' => ?_⟩
  have h1 : 0 < 1 - discF p F := by linarith
  have key : p.c * effortInt p F a + P * penaltyInt p F a ≤
      p.c * effortInt p F a' + P * penaltyInt p F a' := by
    rw [agentCost_eq p hp F hF P a ha, agentCost_eq p hp F hF P a' ha']
    obtain ⟨C, hC⟩ := admissible_bound ha'
    refine setIntegral_mono_on ?_ ?_ measurableSet_Ioi fun t ht => hpt t ht (a' t) (ha'.2.1 t)
    · obtain ⟨C0, hC0⟩ := admissible_bound ha
      exact ((intOn_bdd_S p hp F a ha.1 C0 hC0).const_mul _).add
        ((intOn_bdd_Q p hp F _ (measurable_exp_neg_a a ha) 1 (exp_neg_bound ha)).const_mul _)
    · exact ((intOn_bdd_S p hp F a' ha'.1 C hC).const_mul _).add
        ((intOn_bdd_Q p hp F _ (measurable_exp_neg_a a' ha') 1 (exp_neg_bound ha')).const_mul _)
  unfold agentPayoff
  have : p.c * effortInt p F a / (1 - discF p F) + P * penaltyInt p F a / (1 - discF p F) ≤
      p.c * effortInt p F a' / (1 - discF p F) + P * penaltyInt p F a' / (1 - discF p F) := by
    rw [← add_div, ← add_div]; exact div_le_div_of_nonneg_right key h1.le
  linarith

lemma effortInt_nonneg (p : Params) (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : F (Iic 0) = 0) (a : Effort) (ha : Admissible a) : 0 ≤ effortInt p F a := by
  rw [effortInt_eq p F hF a ha]
  exact setIntegral_nonneg measurableSet_Ioi fun t _ =>
    mul_nonneg (mul_nonneg (ha.2.1 t) (Real.exp_pos _).le) (Sv_nonneg F t)

lemma penaltyInt_nonneg (p : Params) (hp : Standing p) (F : Measure ℝ) [IsProbabilityMeasure F]
    (hF : F (Iic 0) = 0) (a : Effort) (ha : Admissible a) : 0 ≤ penaltyInt p F a := by
  rw [penaltyInt_eq p hp F hF a ha]
  exact mul_nonneg hp.hlam.le (setIntegral_nonneg measurableSet_Ioi fun t _ =>
    mul_nonneg (Real.exp_pos _).le (Qv_nonneg p F t))

/-- With binding participation, the reduced payoff is achievable. -/
lemma achievable_reduced (p : Params) (hp : Standing p) (K : ℝ)
    (law : ℝ → Measure ℝ) {v P : ℝ} (hv : 0 < v) (hP : 0 ≤ P) (a : Effort)
    (hopt : AgentOptimal p (law v) P a) (hδ : discF p (law v) < 1)
    (hE : 0 ≤ effortInt p (law v) a) (hPen : 0 ≤ penaltyInt p (law v) a) :
    Achievable p K law (reducedPayoff p K v (law v) a) := by
  have h1 : 0 < 1 - discF p (law v) := by linarith
  have hr0 : p.r ≠ 0 := hp.hr.ne'
  have h10 : 1 - discF p (law v) ≠ 0 := h1.ne'
  set w := p.r * (p.pibar + (p.c * effortInt p (law v) a + P * penaltyInt p (law v) a) /
    (1 - discF p (law v))) with hw
  have hw0 : 0 ≤ w := mul_nonneg hp.hr.le (add_nonneg hp.hpibar.le
    (div_nonneg (add_nonneg (mul_nonneg hp.hc.le hE) (mul_nonneg hP hPen)) h1.le))
  refine ⟨v, P, w, a, hv, hP, hw0, hopt, ?_, ?_⟩
  · unfold agentPayoff
    rw [hw]
    have : p.r * (p.pibar + (p.c * effortInt p (law v) a + P * penaltyInt p (law v) a) /
        (1 - discF p (law v))) / p.r = p.pibar + (p.c * effortInt p (law v) a +
          P * penaltyInt p (law v) a) / (1 - discF p (law v)) := by
      field_simp
    rw [this, add_div]; linarith
  · unfold principalPayoff reducedPayoff mubar
    rw [hw]
    field_simp
    ring

lemma final_cmp {c r δ A Ψ X : ℝ} (hc : 0 < c) (hr : 0 < r) (hδ : 0 < 1 - δ) (hΨ : Ψ < 0)
    (hX : r * X = (1 + A) * (1 - δ) + Ψ) : c * X / (1 - δ) < c * (1 + A) / r := by
  rw [div_lt_div_iff₀ hδ hr]
  have h2 : c * X * r = c * (1 + A) * (1 - δ) + c * Ψ := by linear_combination c * hX
  linarith [mul_neg_of_pos_of_neg hc hΨ]

lemma discF_hyb_lt (p : Params) (hp : Standing p) {q v : ℝ} (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hv : 0 < v) : discF p (hybridLaw q v) < 1 := by
  rw [discF_hyb p hp hq0.le hq1 hv]
  have hρ : 0 < p.r + v := add_pos hp.hr hv
  have hu : Real.exp (-(p.r * (q / v))) < 1 :=
    (Real.exp_lt_exp.2 (show -(p.r * (q / v)) < 0 by
      have := mul_pos hp.hr (div_pos hq0 hv); linarith)).trans_eq Real.exp_zero
  have hb : v / (p.r + v) ≤ 1 := (div_le_one hρ).2 (by linarith [hp.hr])
  have hb0 : 0 ≤ v / (p.r + v) := (div_pos hv hρ).le
  have h1 : q + (1 - q) * (v / (p.r + v)) ≤ 1 := by nlinarith
  have h2 : 0 ≤ q + (1 - q) * (v / (p.r + v)) := by nlinarith
  nlinarith [Real.exp_pos (-(p.r * (q / v)))]

lemma c2c_effort (p : Params) (hp : Standing p) (K : ℝ) {v : ℝ} (hv : 0 < v)
    (hcB : p.c < p.L * p.lam / (p.r + v)) :
    ∃ xH, AchievableHybrid p K xH ∧ Grand p K v < xH := by
  have hr := hp.hr
  have hρ : 0 < p.r + v := add_pos hr hv
  have hLl : 0 < p.L * p.lam := mul_pos hp.hL hp.hlam
  set κ := p.c * (p.r + v) / (p.L * p.lam) with hκdef
  have hκ0 : 0 < κ := div_pos (mul_pos hp.hc hρ) hLl
  have hκ1 : κ < 1 := by
    rw [hκdef, div_lt_one hLl]; rw [lt_div_iff₀ hρ] at hcB; linarith
  set x := min (min (1 / 2) (v / p.r / 8)) (min (p.r / v) (1 - κ)) with hxdef
  have hx0 : 0 < x :=
    lt_min (lt_min (by norm_num) (by positivity)) (lt_min (by positivity) (by linarith))
  have hx1 : x ≤ 1 / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hxβ : x ≤ v / p.r / 8 := (min_le_left _ _).trans (min_le_right _ _)
  have hxq : x ≤ p.r / v := (min_le_right _ _).trans (min_le_left _ _)
  have hxk : x ≤ 1 - κ := (min_le_right _ _).trans (min_le_right _ _)
  set q := v * x / p.r with hqdef
  have hq0 : 0 < q := by positivity
  have hq1 : q ≤ 1 := by
    rw [hqdef, div_le_one hr]; rw [le_div_iff₀ hv] at hxq; linarith
  have hrq : p.r * (q / v) = x := by rw [hqdef]; field_simp
  have hd : 0 < q / v := div_pos hq0 hv
  haveI := hyb_prob hq0.le hq1 hv
  have hF : hybridLaw q v (Iic 0) = 0 := hyb_Iic_zero hq0 hv
  have hδeq := discF_hyb p hp hq0.le hq1 hv
  have hδ : discF p (hybridLaw q v) < 1 := discF_hyb_lt p hp hq0 hq1 hv
  have hx1' : 0 < 1 + p.r * (q / v) := by rw [hrq]; linarith
  have hadm : κ * Real.exp (p.r * (q / v)) ≤ 1 + p.r * (q / v) := by
    rw [hrq]
    have h1 := Real.exp_bound_div_one_sub_of_interval' hx0 (by linarith)
    have h3 : κ * Real.exp x ≤ κ * (1 / (1 - x)) := mul_le_mul_of_nonneg_left h1.le hκ0.le
    have h2 : κ * (1 / (1 - x)) ≤ 1 := by
      rw [mul_one_div, div_le_one (by linarith)]; linarith
    linarith
  have ha := aH_admissible hr hd rfl hκ0 hκ1.le hadm
  have hP : 0 ≤ p.L / v := div_nonneg hp.hL.le hv.le
  have hE : Real.exp (p.r * (q / v)) = (Real.exp (-(p.r * (q / v))))⁻¹ := by
    rw [Real.exp_neg, inv_inv]
  have hu0 : Real.exp (-(p.r * (q / v))) ≠ 0 := (Real.exp_pos _).ne'
  have hv0 : v ≠ 0 := hv.ne'
  have hρ0 : p.r + v ≠ 0 := hρ.ne'
  have hL0 : p.L ≠ 0 := hp.hL.ne'
  have hl0 : p.lam ≠ 0 := hp.hlam.ne'
  have hvq : v + p.r * q ≠ 0 := by positivity
  have hopt : AgentOptimal p (hybridLaw q v) (p.L / v) (aH p.r κ (p.r * (q / v)) (q / v)) := by
    refine agentOpt_of_pointwise p hp _ hF hδ _ _ ha fun t ht b _ => ?_
    have hb : p.L / v * p.lam * Qv p (hybridLaw q v) t *
        Real.exp (-(aH p.r κ (p.r * (q / v)) (q / v) t)) =
        p.c * (Real.exp (-(p.r * t)) * Sv (hybridLaw q v) t) := by
      rcases lt_or_ge t (q / v) with htd | htd
      · rw [Qv_hyb_lt p hv htd, Sv_hyb_lt hq0.le hq1 hv htd,
          exp_neg_aH_lt hκ0 hx1' ht.le htd, hδeq, hE, hκdef]
        field_simp
        ring
      · rw [Qv_hyb_ge p hp hq0.le hq1 hv htd, Sv_hyb_ge hq0.le hq1 hv htd, aH_ge htd, neg_neg,
          Real.exp_log hκ0]
        have hX : Real.exp (-(p.r * (q / v))) * Real.exp (-((p.r + v) * (t - q / v))) =
            Real.exp (-(p.r * t)) * Real.exp (-(v * (t - q / v))) := by
          rw [← Real.exp_add, ← Real.exp_add]; ring_nf
        have hcoef : p.L / v * p.lam * (v / (p.r + v)) * κ = p.c := by
          rw [hκdef]; field_simp
        calc p.L / v * p.lam * ((1 - q) * Real.exp (-(p.r * (q / v))) *
              (v / (p.r + v) * Real.exp (-((p.r + v) * (t - q / v))))) * κ
            = (p.L / v * p.lam * (v / (p.r + v)) * κ) * (1 - q) *
              (Real.exp (-(p.r * (q / v))) * Real.exp (-((p.r + v) * (t - q / v)))) := by ring
          _ = p.c * (Real.exp (-(p.r * t)) * ((1 - q) * Real.exp (-(v * (t - q / v))))) := by
            rw [hcoef, hX]; ring
    have hmin := pointwise_min (c := p.c) (α := Real.exp (-(p.r * t)) * Sv (hybridLaw q v) t)
      (β := p.L / v * p.lam * Qv p (hybridLaw q v) t)
      (mul_nonneg hp.hc.le (mul_nonneg (Real.exp_pos _).le (Sv_nonneg _ _))) hb b
    calc p.c * (aH p.r κ (p.r * (q / v)) (q / v) t * Real.exp (-(p.r * t)) *
            Sv (hybridLaw q v) t) + p.L / v * p.lam *
            (Real.exp (-(aH p.r κ (p.r * (q / v)) (q / v) t)) * Qv p (hybridLaw q v) t)
        = p.c * (Real.exp (-(p.r * t)) * Sv (hybridLaw q v) t) *
            aH p.r κ (p.r * (q / v)) (q / v) t + p.L / v * p.lam * Qv p (hybridLaw q v) t *
            Real.exp (-(aH p.r κ (p.r * (q / v)) (q / v) t)) := by ring
      _ ≤ _ := hmin
      _ = _ := by ring
  refine ⟨reducedPayoff p K v (hybridLaw q v) (aH p.r κ (p.r * (q / v)) (q / v)),
    ⟨q, hq0.le, hq1, achievable_reduced p hp K (hybridLaw q) hv hP _ hopt hδ
      (effortInt_nonneg p _ hF _ ha) (penaltyInt_nonneg p hp _ hF _ ha)⟩, ?_⟩
  -- the value comparison
  have hEv := effortInt_eq p (hybridLaw q v) hF _ ha
  rw [effortH_val p hp hq0 hq1 hv] at hEv
  have hLv := lossInt_eq p hp (hybridLaw q v) hF _ ha
  rw [lossH_val p hp hq0 hq1 hv hκ0] at hLv
  have hm : mfun p.c (p.L * p.lam / (p.r + v)) = p.c * (1 + -Real.log κ) := by
    rw [mfun, if_pos hcB, hκdef, ← Real.log_inv]
    congr 3
    field_simp
  have hΨ := psi_neg p.r v (p.r * (q / v)) hr hv (by rw [hrq]; exact hx0) (by rw [hrq]; exact hx1)
    (by rw [hrq]; exact hxβ)
  have hX := effort_algebra p.r v q κ hr hv hκ0 hx1'
  rw [← hδeq] at hX
  have hδ1 : 0 < 1 - discF p (hybridLaw q v) := by linarith
  have hfc := final_cmp hp.hc hr hδ1 hΨ hX
  have hc0 : p.c ≠ 0 := hp.hc.ne'
  have hsplit : ∀ E W : ℝ, p.c * E / (1 - discF p (hybridLaw q v)) +
      p.L * (p.lam * W) / (1 - discF p (hybridLaw q v)) =
      p.c * (E + (p.r + v) / κ * W) / (1 - discF p (hybridLaw q v)) := by
    intro E W
    rw [hκdef]
    field_simp
  have key : p.c * effortInt p (hybridLaw q v) (aH p.r κ (p.r * (q / v)) (q / v)) /
      (1 - discF p (hybridLaw q v)) + p.L * lossInt p (hybridLaw q v)
        (aH p.r κ (p.r * (q / v)) (q / v)) / (1 - discF p (hybridLaw q v)) <
      p.c * (1 + -Real.log κ) / p.r := by
    rw [hEv, hLv, hsplit]; exact hfc
  unfold reducedPayoff Grand
  rw [hm]
  linarith [key]

lemma c2c_zero (p : Params) (hp : Standing p) (K : ℝ) {v : ℝ} (hv : 0 < v)
    (hcB : ¬ p.c < p.L * p.lam / (p.r + v)) :
    ∃ xH, AchievableHybrid p K xH ∧ Grand p K v < xH := by
  have hr := hp.hr
  have hρ : 0 < p.r + v := add_pos hr hv
  have hLl : 0 < p.L * p.lam := mul_pos hp.hL hp.hlam
  set x := min (1 / 2) (p.r / v) with hxdef
  have hx0 : 0 < x := lt_min (by norm_num) (by positivity)
  have hx1 : x ≤ 1 / 2 := min_le_left _ _
  have hxq : x ≤ p.r / v := min_le_right _ _
  set q := v * x / p.r with hqdef
  have hq0 : 0 < q := by positivity
  have hq1 : q ≤ 1 := by
    rw [hqdef, div_le_one hr]; rw [le_div_iff₀ hv] at hxq; linarith
  have hrq : p.r * (q / v) = x := by rw [hqdef]; field_simp
  haveI := hyb_prob hq0.le hq1 hv
  have hF : hybridLaw q v (Iic 0) = 0 := hyb_Iic_zero hq0 hv
  have hδeq := discF_hyb p hp hq0.le hq1 hv
  have hδ : discF p (hybridLaw q v) < 1 := discF_hyb_lt p hp hq0 hq1 hv
  have hδ1 : 0 < 1 - discF p (hybridLaw q v) := by linarith
  have ha : Admissible (fun _ : ℝ => (0:ℝ)) :=
    ⟨measurable_const, fun _ => le_rfl, 0, fun _ => le_rfl⟩
  have hopt : AgentOptimal p (hybridLaw q v) 0 (fun _ => 0) := by
    refine agentOpt_of_pointwise p hp _ hF hδ 0 _ ha fun t ht b hb => ?_
    have := mul_nonneg hp.hc.le (mul_nonneg (mul_nonneg hb (Real.exp_pos (-(p.r * t))).le)
      (Sv_nonneg (hybridLaw q v) t))
    nlinarith [this]
  refine ⟨reducedPayoff p K v (hybridLaw q v) (fun _ => 0),
    ⟨q, hq0.le, hq1, achievable_reduced p hp K (hybridLaw q) hv le_rfl _ hopt hδ
      (effortInt_nonneg p _ hF _ ha) (penaltyInt_nonneg p hp _ hF _ ha)⟩, ?_⟩
  have hE0 : effortInt p (hybridLaw q v) (fun _ => 0) = 0 := by simp [effortInt]
  obtain ⟨WZ, hWZ⟩ : ∃ W, ∫ t in Ioi 0, Wv p (hybridLaw q v) t = W := ⟨_, rfl⟩
  have hLv := lossInt_eq p hp (hybridLaw q v) hF _ ha
  simp only [neg_zero, Real.exp_zero, one_mul] at hLv
  rw [hWZ] at hLv
  have hW2 := lossZ_val p hp hq0 hq1 hv
  rw [hWZ] at hW2
  have hZ := zero_algebra p.r v q hr hv
  rw [← hδeq, ← hW2] at hZ
  have hpos : 0 < v / p.r * Real.exp (-(p.r * (q / v))) *
      (1 + p.r * (q / v) + (p.r * (q / v)) ^ 2 - (Real.exp (-(p.r * (q / v))))⁻¹) := by
    rw [Real.exp_neg, inv_inv, hrq]
    have := exp_lt_quad hx0 hx1
    exact mul_pos (mul_pos (div_pos hv hr) (inv_pos.2 (Real.exp_pos _))) (by linarith)
  have hm : mfun p.c (p.L * p.lam / (p.r + v)) = p.L * p.lam / (p.r + v) := by
    rw [mfun, if_neg hcB]
  have h1 : WZ / (1 - discF p (hybridLaw q v)) < 1 / (p.r * (p.r + v)) := by
    rw [div_lt_div_iff₀ hδ1 (by positivity)]; linarith
  have h2 := mul_lt_mul_of_pos_left h1 hLl
  have e1 : p.L * (p.lam * WZ) / (1 - discF p (hybridLaw q v)) =
      p.L * p.lam * (WZ / (1 - discF p (hybridLaw q v))) := by ring
  have e2 : p.L * p.lam / (p.r + v) / p.r = p.L * p.lam * (1 / (p.r * (p.r + v))) := by
    rw [div_div, mul_one_div, mul_comm (p.r + v) p.r]
  unfold reducedPayoff Grand
  rw [hm, hE0, hLv]
  have e3 : p.c * 0 / (1 - discF p (hybridLaw q v)) = 0 := by simp
  rw [e3]
  linarith

lemma c2c (p : Params) (hp : Standing p) (K : ℝ) {v : ℝ} (hv : 0 < v) :
    ∃ xH, AchievableHybrid p K xH ∧ Grand p K v < xH := by
  by_cases hcB : p.c < p.L * p.lam / (p.r + v)
  · exact c2c_effort p hp K hv hcB
  · exact c2c_zero p hp K hv hcB

/-- C2: some hybrid payoff beats every random payoff. -/
theorem C2 (p : Params) (hp : Standing p) (K : ℝ) (hK : 0 < K) :
    ∃ xH, AchievableHybrid p K xH ∧ ∀ xR, Achievable p K randomLaw xR → xR < xH := by
  obtain ⟨vs, hvs, hmax⟩ := Grand_max p hp K hK
  obtain ⟨xH, hH, hlt⟩ := c2c p hp K hvs
  refine ⟨xH, hH, fun xR hR => ?_⟩
  obtain ⟨v, hv, hle⟩ := random_le_Grand p hp K xR hR
  exact lt_of_le_of_lt (hle.trans (hmax v hv)) hlt

/-! ## C1: periodic optimum -/

/-! ### The periodic cost function -/

/-- Best-response effort of the agent under periodic inspection, `max 0 (b + r t)`. -/
noncomputable def mb (r b t : ℝ) : ℝ := max 0 (b + r * t)

/-- Cycle cost numerator. -/
noncomputable def Nper (r c M T b : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..T, (c * mb r b t * Real.exp (-(r * t)) +
    M / r * Real.exp (-(mb r b t)) * (Real.exp (-(r * t)) - Real.exp (-(r * T))))

/-- Total discounted cost (to be minimised). -/
noncomputable def Gper (r c M K T b : ℝ) : ℝ :=
  Nper r c M T b / (1 - Real.exp (-(r * T))) + K / (Real.exp (r * T) - 1)

lemma mb_cont (r : ℝ) : Continuous fun p : ℝ × ℝ => mb r p.1 p.2 := by
  unfold mb; fun_prop

lemma mb_nonneg (r b t : ℝ) : 0 ≤ mb r b t := le_max_left _ _

lemma integrand_cont (r c M T b : ℝ) : Continuous fun t => c * mb r b t * Real.exp (-(r * t)) +
    M / r * Real.exp (-(mb r b t)) * (Real.exp (-(r * t)) - Real.exp (-(r * T))) := by
  have : Continuous fun t => mb r b t := (mb_cont r).comp (continuous_const.prodMk continuous_id)
  fun_prop

lemma Nper_nonneg {r c M T : ℝ} (b : ℝ) (hr : 0 < r) (hc : 0 < c) (hM : 0 < M) (hT : 0 ≤ T) :
    0 ≤ Nper r c M T b := by
  unfold Nper
  refine intervalIntegral.integral_nonneg hT fun t ht => ?_
  have h1 : Real.exp (-(r * T)) ≤ Real.exp (-(r * t)) := Real.exp_le_exp.2 (by nlinarith [ht.2])
  have := mb_nonneg r b t
  have h2 : 0 ≤ M / r := div_nonneg hM.le hr.le
  have h3 := Real.exp_pos (-(r * t))
  have h4 := Real.exp_pos (-(mb r b t))
  have : 0 ≤ c * mb r b t * Real.exp (-(r * t)) := by positivity
  have : 0 ≤ M / r * Real.exp (-(mb r b t)) * (Real.exp (-(r * t)) - Real.exp (-(r * T))) :=
    mul_nonneg (by positivity) (by linarith)
  linarith

/-- Raising effort beyond the first best only adds cost. -/
lemma Nper_clamp_top {r c M T b : ℝ} (hr : 0 < r) (hc : 0 < c) (hM : r * c < M) (hT : 0 ≤ T)
    (hb : Real.log (M / (r * c)) ≤ b) :
    Nper r c M T (Real.log (M / (r * c))) ≤ Nper r c M T b := by
  set b0 := Real.log (M / (r * c)) with hb0
  have hrc : 0 < r * c := mul_pos hr hc
  have hM0 : 0 < M := hrc.trans hM
  have hb0pos : 0 < b0 := Real.log_pos (by rw [one_lt_div hrc]; exact hM)
  have heb0 : Real.exp (-b0) = r * c / M := by
    rw [Real.exp_neg, hb0, Real.exp_log (div_pos hM0 hrc), inv_div]
  unfold Nper
  refine intervalIntegral.integral_mono_on hT ((integrand_cont r c M T b0).intervalIntegrable _ _)
    ((integrand_cont r c M T b).intervalIntegrable _ _) fun t ht => ?_
  have ht0 : 0 ≤ t := ht.1
  have hm1 : mb r b0 t = b0 + r * t := max_eq_right (by nlinarith)
  have hm2 : mb r b t = b + r * t := max_eq_right (by nlinarith)
  rw [hm1, hm2]
  set e := Real.exp (-(r * t)) with he
  set u := Real.exp (-(r * T)) with hu
  have hue : u ≤ e := Real.exp_le_exp.2 (by nlinarith [ht.2])
  have hu0 : 0 < u := Real.exp_pos _
  have he1 : e ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have hE1 : Real.exp (-(b0 + r * t)) = r * c / M * e := by
    rw [show -(b0 + r * t) = -b0 + -(r * t) by ring, Real.exp_add, heb0]
  have hE2 : Real.exp (-(b + r * t)) = Real.exp (-(b0 + r * t)) * Real.exp (-(b - b0)) := by
    rw [← Real.exp_add]; ring_nf
  have hd := Real.add_one_le_exp (-(b - b0))
  rw [hE2, hE1]
  have key : M / r * (r * c / M * e) * (e - u) * (1 - Real.exp (-(b - b0))) ≤
      c * e * ((b + r * t) - (b0 + r * t)) := by
    have e1 : M / r * (r * c / M * e) = c * e := by field_simp
    rw [e1]
    have h5 : 1 - Real.exp (-(b - b0)) ≤ b - b0 := by linarith
    have h6 : 0 ≤ 1 - Real.exp (-(b - b0)) := by
      have := Real.exp_le_one_iff.2 (show -(b - b0) ≤ 0 by linarith); linarith
    have h7 : (e - u) * (1 - Real.exp (-(b - b0))) ≤ 1 * (b - b0) :=
      mul_le_mul (by linarith) h5 h6 zero_le_one
    have h8 : 0 ≤ c * e := by positivity
    nlinarith
  nlinarith

/-- Below `-r T'` there is no effort on `[0, T]`. -/
lemma Nper_clamp_bot {r c M T T' b : ℝ} (hr : 0 < r) (hT : 0 ≤ T) (hTT : T ≤ T')
    (hb : b ≤ -(r * T')) : Nper r c M T b = Nper r c M T (-(r * T')) := by
  unfold Nper
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hT] at ht
  have h1 : mb r b t = 0 := max_eq_left (by nlinarith [ht.2])
  have h2 : mb r (-(r * T')) t = 0 := max_eq_left (by nlinarith [ht.2])
  simp only [h1, h2]

/-- Uniform bound on the cycle cost for `b ≤ b0`. -/
lemma Nper_le {r c M T b b0 : ℝ} (hr : 0 < r) (hc : 0 < c) (hM : 0 < M) (hT : 0 ≤ T)
    (hb0 : 0 ≤ b0) (hb : b ≤ b0) : Nper r c M T b ≤ (c * b0 + c + M / r) / r := by
  have hbound : Nper r c M T b ≤ ∫ t in (0:ℝ)..T,
      (c * b0 * Real.exp (-(r * t)) + c * r * (t * Real.exp (-(r * t))) +
        M / r * Real.exp (-(r * t))) := by
    unfold Nper
    refine intervalIntegral.integral_mono_on hT ((integrand_cont r c M T b).intervalIntegrable _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _) fun t ht => ?_
    have ht0 : 0 ≤ t := ht.1
    have hm : mb r b t ≤ b0 + r * t := max_le (by nlinarith) (by linarith)
    have hm0 := mb_nonneg r b t
    have he := Real.exp_pos (-(r * t))
    have hu := Real.exp_pos (-(r * T))
    have hem : Real.exp (-(mb r b t)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have hM' : 0 ≤ M / r := div_nonneg hM.le hr.le
    have h1 : c * mb r b t * Real.exp (-(r * t)) ≤ c * (b0 + r * t) * Real.exp (-(r * t)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hc.le) he.le
    have h2 : M / r * Real.exp (-(mb r b t)) * (Real.exp (-(r * t)) - Real.exp (-(r * T))) ≤
        M / r * Real.exp (-(r * t)) := by
      have h3 : Real.exp (-(mb r b t)) * (Real.exp (-(r * t)) - Real.exp (-(r * T))) ≤
          1 * Real.exp (-(r * t)) :=
        mul_le_mul hem (by linarith) (by
          have : Real.exp (-(r * T)) ≤ Real.exp (-(r * t)) := Real.exp_le_exp.2 (by nlinarith [ht.2])
          linarith) zero_le_one
      rw [mul_assoc]; nlinarith
    nlinarith
  refine hbound.trans ?_
  rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_exp_zero_lin _ _ hr.ne', integral_t_exp _ _ hr]
  have hu := Real.exp_pos (-(r * T))
  have hu1 : Real.exp (-(r * T)) * (1 + r * T) ≥ 0 := by positivity
  have k1 : c * b0 * ((1 - Real.exp (-(r * T))) / r) ≤ c * b0 / r := by
    rw [mul_div_assoc']; exact div_le_div_of_nonneg_right (by nlinarith [mul_nonneg hc.le hb0]) hr.le
  have k2 : c * r * ((1 - Real.exp (-(r * T)) * (1 + r * T)) / r ^ 2) ≤ c / r := by
    rw [show c * r * ((1 - Real.exp (-(r * T)) * (1 + r * T)) / r ^ 2) =
      c * (1 - Real.exp (-(r * T)) * (1 + r * T)) / r by field_simp]
    exact div_le_div_of_nonneg_right (by nlinarith) hr.le
  have k3 : M / r * ((1 - Real.exp (-(r * T))) / r) ≤ M / r / r := by
    rw [mul_div_assoc']; exact div_le_div_of_nonneg_right (by
      have : 0 ≤ M / r := div_nonneg hM.le hr.le; nlinarith) hr.le
  have : (c * b0 + c + M / r) / r = c * b0 / r + c / r + M / r / r := by ring
  linarith

/-! ### Monotonicity in the period for long cycles -/

lemma emb_cont (r b : ℝ) : Continuous fun t => Real.exp (-(mb r b t)) := by
  have : Continuous fun t => mb r b t := (mb_cont r).comp (continuous_const.prodMk continuous_id)
  fun_prop

lemma hcost_cont (r c M b : ℝ) : Continuous fun t => c * mb r b t * Real.exp (-(r * t)) +
    M / r * Real.exp (-(mb r b t)) * Real.exp (-(r * t)) := by
  have : Continuous fun t => mb r b t := (mb_cont r).comp (continuous_const.prodMk continuous_id)
  fun_prop

lemma Nper_split (r c M T b : ℝ) :
    Nper r c M T b = (∫ t in (0:ℝ)..T, (c * mb r b t * Real.exp (-(r * t)) +
      M / r * Real.exp (-(mb r b t)) * Real.exp (-(r * t)))) -
      M / r * Real.exp (-(r * T)) * ∫ t in (0:ℝ)..T, Real.exp (-(mb r b t)) := by
  unfold Nper
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
    ((hcost_cont r c M b).intervalIntegrable _ _)
    (((emb_cont r b).const_mul _).intervalIntegrable _ _)]
  congr 1; funext t; ring

/-- Long cycles accumulate either effort cost or unresolved errors. -/
lemma long_cycle_lower {r c M T b : ℝ} (hr : 0 < r) (hc : 0 < c) (hM : r * c ≤ M) (hT : 0 ≤ T) :
    c * r * T / 2 ≤ c * mb r b T + M * ∫ t in (0:ℝ)..T, Real.exp (-(mb r b t)) := by
  have hQ0 : ∀ a z : ℝ, a ≤ z → 0 ≤ ∫ t in a..z, Real.exp (-(mb r b t)) := fun a z h =>
    intervalIntegral.integral_nonneg h fun t _ => (Real.exp_pos _).le
  have hM0 : 0 ≤ M := le_trans (mul_pos hr hc).le hM
  by_cases hb : 0 ≤ b + r * T / 2
  · have hm : r * T / 2 ≤ mb r b T := le_trans (by linarith) (le_max_right _ _)
    have := mul_nonneg hM0 (hQ0 0 T hT)
    nlinarith
  · push Not at hb
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      ((emb_cont r b).intervalIntegrable (μ := volume) 0 (T / 2))
      ((emb_cont r b).intervalIntegrable (μ := volume) (T / 2) T)
    have hfirst : ∫ t in (0:ℝ)..(T / 2), Real.exp (-(mb r b t)) = T / 2 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (1:ℝ)) fun t ht => ?_]
      · simp
      · rw [uIcc_of_le (by linarith)] at ht
        have : mb r b t = 0 := max_eq_left (by nlinarith [ht.2])
        simp [this]
    have h2 := hQ0 (T / 2) T (by linarith)
    have hQ : T / 2 ≤ ∫ t in (0:ℝ)..T, Real.exp (-(mb r b t)) := by linarith
    have := mb_nonneg r b T
    have h3 : M * (T / 2) ≤ M * ∫ t in (0:ℝ)..T, Real.exp (-(mb r b t)) :=
      mul_le_mul_of_nonneg_left hQ hM0
    nlinarith

lemma Gper_hasDerivAt (r c M K b : ℝ) (hr : 0 < r) {T : ℝ} (hT : 0 < T) :
    HasDerivAt (fun T => Gper r c M K T b)
      (Real.exp (-(r * T)) / (1 - Real.exp (-(r * T))) ^ 2 *
        ((c * mb r b T + M * ∫ t in (0:ℝ)..T, Real.exp (-(mb r b t))) *
            (1 - Real.exp (-(r * T))) - r * Nper r c M T b - r * K)) T := by
  have hu1 : Real.exp (-(r * T)) < 1 :=
    (Real.exp_lt_exp.2 (show -(r * T) < 0 by nlinarith)).trans_eq Real.exp_zero
  have hu0 := Real.exp_pos (-(r * T))
  have hfun : (fun T => Gper r c M K T b) = fun T =>
      ((∫ t in (0:ℝ)..T, (c * mb r b t * Real.exp (-(r * t)) +
        M / r * Real.exp (-(mb r b t)) * Real.exp (-(r * t)))) -
        M / r * Real.exp (-(r * T)) * ∫ t in (0:ℝ)..T, Real.exp (-(mb r b t))) /
        (1 - Real.exp (-(r * T))) + K / (Real.exp (r * T) - 1) := by
    funext T; rw [Gper, Nper_split]
  rw [hfun]
  have hH := ((hcost_cont r c M b).integral_hasStrictDerivAt 0 T).hasDerivAt
  have hQ := ((emb_cont r b).integral_hasStrictDerivAt 0 T).hasDerivAt
  have hu : HasDerivAt (fun T => Real.exp (-(r * T))) (Real.exp (-(r * T)) * (-r)) T := by
    have h1 : HasDerivAt (fun t => -(r * t)) (-r) T := by
      simpa using (hasDerivAt_id T).const_mul (-r)
    exact h1.exp
  have hE : HasDerivAt (fun T => Real.exp (r * T)) (Real.exp (r * T) * r) T := by
    have h1 : HasDerivAt (fun t => r * t) r T := by
      simpa using (hasDerivAt_id T).const_mul r
    exact h1.exp
  have hEne : Real.exp (r * T) - 1 ≠ 0 := by
    have hrT : 0 < r * T := by positivity
    have := Real.add_one_lt_exp hrT.ne'; linarith
  have hN := hH.sub ((hu.const_mul (M / r)).mul hQ)
  have hden := (hasDerivAt_const T (1:ℝ)).sub hu
  have hdiv := hN.div hden (by simp only [Pi.sub_apply]; linarith)
  have hK := (hasDerivAt_const T K).div (hE.sub_const 1) hEne
  refine (hdiv.add hK).congr_deriv ?_
  simp only [Pi.sub_apply, Pi.mul_apply]
  rw [Nper_split, show Real.exp (r * T) = (Real.exp (-(r * T)))⁻¹ by rw [Real.exp_neg, inv_inv]]
  have hr0 : r ≠ 0 := hr.ne'
  have hu0' : Real.exp (-(r * T)) ≠ 0 := hu0.ne'
  have h1u : 1 - Real.exp (-(r * T)) ≠ 0 := by linarith
  have h1u' : (Real.exp (-(r * T)))⁻¹ - 1 ≠ 0 := by
    rw [inv_eq_one_div, div_sub_one hu0']; exact div_ne_zero (by linarith) hu0'
  field_simp
  ring

/-- For long cycles the cost increases with the period, uniformly in `b ≤ b0`. -/
lemma Gper_mono_long {r c M K b b0 : ℝ} (hr : 0 < r) (hc : 0 < c) (hM : r * c ≤ M) (hK : 0 ≤ K)
    (hb0 : 0 ≤ b0) (hb : b ≤ b0) :
    MonotoneOn (fun T => Gper r c M K T b)
      (Ici (max (1 / r) (4 * ((c * b0 + c + M / r) / r + K) / c))) := by
  set T3 := max (1 / r) (4 * ((c * b0 + c + M / r) / r + K) / c) with hT3
  have hT3pos : 0 < T3 := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hM0 : 0 < M := lt_of_lt_of_le (mul_pos hr hc) hM
  have hD : ∀ T ∈ Ici T3, HasDerivAt (fun T => Gper r c M K T b) _ T := fun T hT =>
    Gper_hasDerivAt r c M K b hr (lt_of_lt_of_le hT3pos hT)
  refine monotoneOn_of_deriv_nonneg (convex_Ici _) (fun T hT => (hD T hT).continuousAt.continuousWithinAt)
    ?_ ?_
  · rw [interior_Ici]
    exact fun T hT => (hD T (mem_Ici.2 (le_of_lt hT))).differentiableAt.differentiableWithinAt
  · rw [interior_Ici]
    intro T hT
    have hT' : T3 ≤ T := le_of_lt hT
    have hTpos : 0 < T := lt_of_lt_of_le hT3pos hT'
    rw [(hD T (mem_Ici.2 hT')).deriv]
    refine mul_nonneg (div_nonneg (Real.exp_pos _).le (sq_nonneg _)) ?_
    have hrT : 1 ≤ r * T := by
      have h1 : 1 / r ≤ T := le_trans (le_max_left _ _) hT'
      rw [div_le_iff₀ hr] at h1; linarith
    have hu : Real.exp (-(r * T)) ≤ 1 / 2 := by
      have h1 : Real.exp (-(r * T)) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
      have h2 : Real.exp (-1) < 1 / 2 := by
        rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]
        have := Real.exp_one_gt_d9; norm_num; linarith
      linarith
    have hL := long_cycle_lower (b := b) hr hc hM hTpos.le
    have hN := Nper_le hr hc hM0 hTpos.le hb0 hb
    have hT4 : 4 * ((c * b0 + c + M / r) / r + K) ≤ c * T := by
      have h1 : 4 * ((c * b0 + c + M / r) / r + K) / c ≤ T := le_trans (le_max_right _ _) hT'
      rw [div_le_iff₀ hc] at h1; linarith
    set X := c * mb r b T + M * ∫ t in (0:ℝ)..T, Real.exp (-(mb r b t))
    have hX0 : 0 ≤ X := le_trans (by positivity) hL
    have h1 : X / 2 ≤ X * (1 - Real.exp (-(r * T))) := by nlinarith
    have h2 : c * r * T / 4 ≤ X / 2 := by linarith
    have h3 : r * (Nper r c M T b + K) ≤ r * ((c * b0 + c + M / r) / r + K) :=
      mul_le_mul_of_nonneg_left (by linarith) hr.le
    have h4 : 4 * (r * ((c * b0 + c + M / r) / r + K)) ≤ c * r * T := by nlinarith
    nlinarith


/-! ### Existence of a minimiser -/

lemma Nper_cont (r c M : ℝ) : Continuous fun p : ℝ × ℝ => Nper r c M p.1 p.2 := by
  unfold Nper
  have hm : Continuous fun q : (ℝ × ℝ) × ℝ => mb r q.1.2 q.2 :=
    (mb_cont r).comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd)
  have hf : Continuous (Function.uncurry fun (p : ℝ × ℝ) (t : ℝ) =>
      c * mb r p.2 t * Real.exp (-(r * t)) +
        M / r * Real.exp (-(mb r p.2 t)) * (Real.exp (-(r * t)) - Real.exp (-(r * p.1)))) := by
    show Continuous fun q : (ℝ × ℝ) × ℝ => c * mb r q.1.2 q.2 * Real.exp (-(r * q.2)) +
        M / r * Real.exp (-(mb r q.1.2 q.2)) * (Real.exp (-(r * q.2)) - Real.exp (-(r * q.1.1)))
    fun_prop
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hf continuous_fst

lemma one_sub_exp_pos {r T : ℝ} (hr : 0 < r) (hT : 0 < T) : 0 < 1 - Real.exp (-(r * T)) := by
  have : Real.exp (-(r * T)) < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
  linarith

lemma exp_sub_one_pos {r T : ℝ} (hr : 0 < r) (hT : 0 < T) : 0 < Real.exp (r * T) - 1 := by
  have := Real.add_one_lt_exp (mul_pos hr hT).ne'
  have := mul_pos hr hT
  linarith

lemma Gper_contOn (r c M K : ℝ) (hr : 0 < r) :
    ContinuousOn (fun p : ℝ × ℝ => Gper r c M K p.1 p.2) {p | 0 < p.1} := by
  unfold Gper
  refine ContinuousOn.add ?_ ?_
  · exact (Nper_cont r c M).continuousOn.div (by fun_prop)
      fun p hp => (one_sub_exp_pos hr hp).ne'
  · exact continuousOn_const.div (by fun_prop) fun p hp => (exp_sub_one_pos hr hp).ne'

lemma Gper_lower {r c M K T : ℝ} (b : ℝ) (hr : 0 < r) (hc : 0 < c) (hM : 0 < M) (hT : 0 < T) :
    K / (Real.exp (r * T) - 1) ≤ Gper r c M K T b := by
  unfold Gper
  have := div_nonneg (Nper_nonneg b hr hc hM hT.le) (one_sub_exp_pos hr hT).le
  linarith

lemma Gper_clamp_top {r c M K T b : ℝ} (hr : 0 < r) (hc : 0 < c) (hM : r * c < M) (hT : 0 < T) :
    Gper r c M K T (min b (Real.log (M / (r * c)))) ≤ Gper r c M K T b := by
  rcases le_total b (Real.log (M / (r * c))) with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h]
    unfold Gper
    have := div_le_div_of_nonneg_right (Nper_clamp_top hr hc hM hT.le h)
      (one_sub_exp_pos hr hT).le
    linarith

theorem Gper_min {r c M K : ℝ} (hr : 0 < r) (hc : 0 < c) (hM : r * c < M) (hK : 0 < K) :
    ∃ Ts : ℝ, 0 < Ts ∧ ∃ bs : ℝ, ∀ T : ℝ, 0 < T → ∀ b : ℝ,
      Gper r c M K Ts bs ≤ Gper r c M K T b := by
  set b0 := Real.log (M / (r * c)) with hb0
  have hM0 : 0 < M := (mul_pos hr hc).trans hM
  have hb0pos : 0 < b0 := Real.log_pos (by rw [one_lt_div (mul_pos hr hc)]; exact hM)
  set T3 := max (1 / r) (4 * ((c * b0 + c + M / r) / r + K) / c) with hT3
  have hT3pos : 0 < T3 := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  set Gref := Gper r c M K T3 (-(r * T3)) with hGref_def
  have hGref : K / (Real.exp (r * T3) - 1) ≤ Gref := Gper_lower _ hr hc hM0 hT3pos
  have hE3 := exp_sub_one_pos hr hT3pos
  have hGpos : 0 < Gref := lt_of_lt_of_le (div_pos hK hE3) hGref
  have hKG : 0 < K / Gref := div_pos hK hGpos
  set T0 := Real.log (1 + K / Gref) / r with hT0
  have hT0pos : 0 < T0 := div_pos (Real.log_pos (by linarith)) hr
  have heT0 : Real.exp (r * T0) = 1 + K / Gref := by
    rw [show r * T0 = Real.log (1 + K / Gref) by rw [hT0]; field_simp]
    exact Real.exp_log (by linarith)
  have hT0T3 : T0 ≤ T3 := by
    have h1 : K / Gref ≤ Real.exp (r * T3) - 1 := by
      rw [div_le_iff₀ hGpos]; rw [div_le_iff₀ hE3] at hGref; linarith
    have h2 : Real.exp (r * T0) ≤ Real.exp (r * T3) := by rw [heT0]; linarith
    exact le_of_mul_le_mul_left (Real.exp_le_exp.1 h2) hr
  set S : Set (ℝ × ℝ) := Icc T0 T3 ×ˢ Icc (-(r * T3)) b0 with hS
  have hne : S.Nonempty := ⟨(T3, b0), ⟨hT0T3, le_rfl⟩, ⟨by nlinarith, le_rfl⟩⟩
  obtain ⟨⟨Ts, bs⟩, hSs, hmin⟩ := (isCompact_Icc.prod isCompact_Icc).exists_isMinOn hne
    ((Gper_contOn r c M K hr).mono fun p hp => lt_of_lt_of_le hT0pos hp.1.1)
  have hTs : 0 < Ts := lt_of_lt_of_le hT0pos hSs.1.1
  refine ⟨Ts, hTs, bs, ?_⟩
  have hmid : ∀ T, T0 ≤ T → T ≤ T3 → ∀ b, Gper r c M K Ts bs ≤ Gper r c M K T b := by
    intro T h1 h2 b
    have hT : 0 < T := lt_of_lt_of_le hT0pos h1
    have step1 := Gper_clamp_top (K := K) (b := b) hr hc hM hT
    rw [← hb0] at step1
    have step2 : Gper r c M K T (max (min b b0) (-(r * T3))) = Gper r c M K T (min b b0) := by
      rcases le_total (min b b0) (-(r * T3)) with h | h
      · rw [max_eq_right h]; unfold Gper; rw [Nper_clamp_bot hr hT.le h2 h]
      · rw [max_eq_left h]
    have hmem : (T, max (min b b0) (-(r * T3))) ∈ S :=
      ⟨⟨h1, h2⟩, ⟨le_max_right _ _, max_le (min_le_right _ _) (by nlinarith)⟩⟩
    have := isMinOn_iff.1 hmin _ hmem
    simp only at this
    linarith
  intro T hT b
  rcases le_or_gt T0 T with h1 | h1
  · rcases le_or_gt T T3 with h2 | h2
    · exact hmid T h1 h2 b
    · have hmono := Gper_mono_long (K := K) (b := min b b0) hr hc hM.le hK.le hb0pos.le
        (min_le_right _ _)
      rw [← hT3] at hmono
      have h3 := hmono (mem_Ici.2 le_rfl) (mem_Ici.2 h2.le) h2.le
      have h4 := Gper_clamp_top (K := K) (b := b) hr hc hM hT
      rw [← hb0] at h4
      have h5 := hmid T3 hT0T3 le_rfl (min b b0)
      simp only at h3
      linarith
  · have h3 := Gper_lower (K := K) b hr hc hM0 hT
    have h4 : K / (Real.exp (r * T0) - 1) ≤ K / (Real.exp (r * T) - 1) :=
      div_le_div_of_nonneg_left hK.le (exp_sub_one_pos hr hT)
        (by have := Real.exp_le_exp.2 (show r * T ≤ r * T0 by nlinarith); linarith)
    have h5 : K / (Real.exp (r * T0) - 1) = Gref := by
      rw [heT0, add_sub_cancel_left, div_div_cancel₀ hK.ne']
    have h6 := hmid T3 hT0T3 le_rfl (-(r * T3))
    linarith

/-! ## C1: the periodic optimum is attained -/

/-- The agent's best response, extended to be bounded. -/
noncomputable def astar (r b T : ℝ) (t : ℝ) : ℝ := max 0 (b + r * min t T)

lemma astar_admissible (r b T : ℝ) (hr : 0 < r) : Admissible (astar r b T) := by
  refine ⟨?_, fun t => le_max_left _ _, max 0 (b + r * T), fun t => ?_⟩
  · exact (continuous_const.max (continuous_const.add
      (continuous_const.mul (continuous_id.min continuous_const)))).measurable
  · unfold astar
    exact max_le_max le_rfl (by linarith [mul_le_mul_of_nonneg_left (min_le_right t T) hr.le])

lemma astar_eq {r b T t : ℝ} (ht : t ≤ T) : astar r b T t = mb r b t := by
  unfold astar mb; rw [min_eq_left ht]

lemma dirac_Iic_zero {T : ℝ} (hT : 0 < T) : Measure.dirac T (Iic (0:ℝ)) = 0 := by
  have : T ∉ Iic (0:ℝ) := by simpa using hT
  simp [Measure.dirac_apply' _ measurableSet_Iic, this]

lemma discF_per (p : Params) (T : ℝ) : discF p (Measure.dirac T) = Real.exp (-(p.r * T)) := by
  unfold discF; rw [integral_dirac]

lemma effort_per (p : Params) (T : ℝ) (a : Effort) :
    effortInt p (Measure.dirac T) a = ∫ t in (0:ℝ)..T, a t * Real.exp (-(p.r * t)) := by
  unfold effortInt; rw [integral_dirac]

lemma pen_per (p : Params) (T : ℝ) (a : Effort) :
    penaltyInt p (Measure.dirac T) a =
      p.lam * (∫ t in (0:ℝ)..T, Real.exp (-(a t))) * Real.exp (-(p.r * T)) := by
  unfold penaltyInt expCount; rw [integral_dirac]

lemma Sv_per (T t : ℝ) : Sv (Measure.dirac T) t = (Iio T).indicator 1 t := by
  classical
  unfold Sv
  rw [setIntegral_dirac]
  by_cases h : t < T
  · simp [h]
  · simp [h]

lemma Wv_per (p : Params) (hp : Standing p) {T s : ℝ} (hs : 0 < s) :
    Wv p (Measure.dirac T) s = (Iic T).indicator
      (fun s => (Real.exp (-(p.r * s)) - Real.exp (-(p.r * T))) / p.r) s := by
  rw [Wv, Measure.restrict_restrict measurableSet_Ioi, Ioi_inter_Ioi,
    show s ⊔ 0 = s from max_eq_left hs.le]
  have e : (fun t => Real.exp (-(p.r * t)) * Sv (Measure.dirac T) t) =
      (Iio T).indicator (fun t => Real.exp (-(p.r * t))) := by
    funext t; rw [Sv_per]; by_cases h : t < T <;> simp [h]
  rw [e, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio]
  by_cases h : s ≤ T
  · rw [Set.indicator_of_mem (show s ∈ Iic T from h), ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le h, integral_exp_lin _ _ _ hp.hr.ne']
  · push_neg at h
    rw [Set.indicator_of_notMem (show s ∉ Iic T from not_le.2 h), Ioo_eq_empty (not_lt.2 h.le),
      Measure.restrict_empty, integral_zero_measure]

lemma loss_per (p : Params) (hp : Standing p) {T : ℝ} (hT : 0 < T) (a : Effort)
    (ha : Admissible a) :
    lossInt p (Measure.dirac T) a = p.lam * ∫ s in (0:ℝ)..T,
      Real.exp (-(a s)) * ((Real.exp (-(p.r * s)) - Real.exp (-(p.r * T))) / p.r) := by
  rw [lossInt_eq p hp _ (dirac_Iic_zero hT) a ha]
  congr 1
  rw [intervalIntegral.integral_of_le hT.le]
  have e : EqOn (fun s => Real.exp (-(a s)) * Wv p (Measure.dirac T) s)
      ((Ioc 0 T).indicator (fun s => Real.exp (-(a s)) *
        ((Real.exp (-(p.r * s)) - Real.exp (-(p.r * T))) / p.r))) (Ioi 0) := by
    intro s hs
    simp only
    rw [Wv_per p hp hs]
    by_cases h : s ≤ T
    · rw [Set.indicator_of_mem (show s ∈ Iic T from h),
        Set.indicator_of_mem (show s ∈ Ioc 0 T from ⟨hs, h⟩)]
    · rw [Set.indicator_of_notMem (show s ∉ Iic T from h),
        Set.indicator_of_notMem (show s ∉ Ioc 0 T from fun h' => h h'.2), mul_zero]
  rw [setIntegral_congr_fun measurableSet_Ioi e, setIntegral_indicator measurableSet_Ioc,
    inter_eq_right.2 Ioc_subset_Ioi_self]

/-- Pointwise agent cost on `[0, T]`. -/
noncomputable def phiA (p : Params) (T P : ℝ) (t y : ℝ) : ℝ :=
  p.c * Real.exp (-(p.r * t)) * y + P * p.lam * Real.exp (-(p.r * T)) * Real.exp (-y)

lemma phiA_int (p : Params) (T P : ℝ) (a : Effort) (ha : Admissible a) :
    IntervalIntegrable (fun t => phiA p T P t (a t)) volume 0 T := by
  obtain ⟨C, hC⟩ := admissible_bound ha
  have h1 : IntervalIntegrable a volume 0 T := intervalIntegrable_of_bdd a ha.1 C hC 0 T
  have h2 : IntervalIntegrable (fun t => p.c * Real.exp (-(p.r * t)) * a t) volume 0 T :=
    h1.continuousOn_mul (by fun_prop : Continuous fun t => p.c * Real.exp (-(p.r * t))).continuousOn
  have h3 := (exp_neg_a_intervalIntegrable a ha 0 T).const_mul (P * p.lam * Real.exp (-(p.r * T)))
  unfold phiA
  exact h2.add h3

lemma agentPay_per (p : Params) (T P : ℝ) (a : Effort) (ha : Admissible a) :
    agentPayoff p (Measure.dirac T) a P 0 =
      -(∫ t in (0:ℝ)..T, phiA p T P t (a t)) / (1 - Real.exp (-(p.r * T))) := by
  obtain ⟨C, hC⟩ := admissible_bound ha
  have h1 : IntervalIntegrable a volume 0 T := intervalIntegrable_of_bdd a ha.1 C hC 0 T
  have h2 : IntervalIntegrable (fun t => p.c * Real.exp (-(p.r * t)) * a t) volume 0 T :=
    h1.continuousOn_mul (by fun_prop : Continuous fun t => p.c * Real.exp (-(p.r * t))).continuousOn
  have h3 := (exp_neg_a_intervalIntegrable a ha 0 T).const_mul (P * p.lam * Real.exp (-(p.r * T)))
  have hI : ∫ t in (0:ℝ)..T, phiA p T P t (a t) =
      p.c * (∫ t in (0:ℝ)..T, a t * Real.exp (-(p.r * t))) +
        P * (p.lam * (∫ t in (0:ℝ)..T, Real.exp (-(a t))) * Real.exp (-(p.r * T))) := by
    have e1 : ∫ t in (0:ℝ)..T, p.c * Real.exp (-(p.r * t)) * a t =
        p.c * ∫ t in (0:ℝ)..T, a t * Real.exp (-(p.r * t)) := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun t _ => by ring
    have e2 : ∫ t in (0:ℝ)..T, P * p.lam * Real.exp (-(p.r * T)) * Real.exp (-(a t)) =
        P * p.lam * Real.exp (-(p.r * T)) * ∫ t in (0:ℝ)..T, Real.exp (-(a t)) :=
      intervalIntegral.integral_const_mul _ _
    unfold phiA
    rw [intervalIntegral.integral_add h2 h3, e1, e2]
    ring
  unfold agentPayoff
  rw [effort_per, pen_per, discF_per, hI]
  ring

lemma pt_min {A β m : ℝ} (hA : 0 < A) (hβ : 0 ≤ β)
    (hm : (0 ≤ m ∧ β * Real.exp (-m) = A) ∨ (m = 0 ∧ β ≤ A)) {y : ℝ} (hy : 0 ≤ y) :
    A * m + β * Real.exp (-m) ≤ A * y + β * Real.exp (-y) ∧
      (A * y + β * Real.exp (-y) ≤ A * m + β * Real.exp (-m) → y = m) := by
  rcases hm with ⟨_, he⟩ | ⟨rfl, hβA⟩
  · have e : β * Real.exp (-y) = A * Real.exp (m - y) := by
      rw [← he, mul_assoc, ← Real.exp_add]; ring_nf
    rw [e, he]
    constructor
    · have := Real.add_one_le_exp (m - y)
      nlinarith [mul_le_mul_of_nonneg_left this hA.le]
    · intro h
      by_contra hne
      have := Real.add_one_lt_exp (sub_ne_zero.2 (Ne.symm hne))
      nlinarith [mul_lt_mul_of_pos_left this hA]
  · simp only [mul_zero, neg_zero, Real.exp_zero, mul_one, zero_add]
    have hey : 1 - Real.exp (-y) ≤ y := by have := Real.add_one_le_exp (-y); linarith
    have hey0 : 0 ≤ 1 - Real.exp (-y) := by
      have := Real.exp_le_one_iff.2 (neg_nonpos.2 hy); linarith
    constructor
    · nlinarith [mul_le_mul_of_nonneg_right hβA hey0, mul_le_mul_of_nonneg_left hey hA.le]
    · intro h
      by_contra hne
      have hy0 : 0 < y := lt_of_le_of_ne hy (Ne.symm hne)
      have hlt : 1 - Real.exp (-y) < y := by
        have := Real.add_one_lt_exp (neg_ne_zero.2 hy0.ne'); linarith
      nlinarith [mul_le_mul_of_nonneg_right hβA hey0, mul_lt_mul_of_pos_left hlt hA]

/-- The penalty-implied effort intercept. -/
noncomputable def bOf (p : Params) (P T : ℝ) : ℝ :=
  if 0 < P then Real.log (P * p.lam / p.c) - p.r * T else -(p.r * T)

lemma pt_cond (p : Params) (hp : Standing p) {P T t : ℝ} (hP : 0 ≤ P) (ht0 : 0 ≤ t)
    (htT : t ≤ T) :
    (0 ≤ mb p.r (bOf p P T) t ∧ P * p.lam * Real.exp (-(p.r * T)) *
        Real.exp (-(mb p.r (bOf p P T) t)) = p.c * Real.exp (-(p.r * t))) ∨
      (mb p.r (bOf p P T) t = 0 ∧
        P * p.lam * Real.exp (-(p.r * T)) ≤ p.c * Real.exp (-(p.r * t))) := by
  rcases hP.lt_or_eq with hP | hP
  · set b := bOf p P T with hb
    have hb' : b = Real.log (P * p.lam / p.c) - p.r * T := by rw [hb, bOf, if_pos hP]
    have hβ : P * p.lam * Real.exp (-(p.r * T)) = p.c * Real.exp b := by
      have hc := hp.hc; have hl := hp.hlam
      rw [hb', Real.exp_sub, Real.exp_log (by positivity), Real.exp_neg]
      field_simp
    rw [hβ]
    rcases le_total 0 (b + p.r * t) with h | h
    · left
      have hm : mb p.r b t = b + p.r * t := max_eq_right h
      rw [hm]
      refine ⟨h, ?_⟩
      rw [mul_assoc, ← Real.exp_add, show b + -(b + p.r * t) = -(p.r * t) by ring]
    · right
      have hm : mb p.r b t = 0 := max_eq_left h
      refine ⟨hm, ?_⟩
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith)) hp.hc.le
  · right
    subst hP
    have hbo : bOf p 0 T = -(p.r * T) := by simp [bOf]
    refine ⟨?_, by rw [zero_mul, zero_mul]; have := hp.hc; positivity⟩
    rw [hbo]; unfold mb
    exact max_eq_left (by nlinarith [mul_le_mul_of_nonneg_left htT hp.hr.le])

lemma pt_min_per (p : Params) (hp : Standing p) {P T t y : ℝ} (hP : 0 ≤ P) (ht0 : 0 ≤ t)
    (htT : t ≤ T) (hy : 0 ≤ y) :
    phiA p T P t (mb p.r (bOf p P T) t) ≤ phiA p T P t y ∧
      (phiA p T P t y ≤ phiA p T P t (mb p.r (bOf p P T) t) → y = mb p.r (bOf p P T) t) := by
  have hA : 0 < p.c * Real.exp (-(p.r * t)) := mul_pos hp.hc (Real.exp_pos _)
  have hβ : 0 ≤ P * p.lam * Real.exp (-(p.r * T)) :=
    mul_nonneg (mul_nonneg hP hp.hlam.le) (Real.exp_pos _).le
  exact pt_min hA hβ (pt_cond p hp hP ht0 htT) hy

lemma mb_cont1 (r b : ℝ) : Continuous fun t => mb r b t :=
  (mb_cont r).comp (continuous_const.prodMk continuous_id)

lemma br_unique (p : Params) (hp : Standing p) {T P : ℝ} (hT : 0 < T) (hP : 0 ≤ P) (a : Effort)
    (hopt : AgentOptimal p (Measure.dirac T) P a) :
    ∀ᵐ t, t ∈ Ioc 0 T → a t = mb p.r (bOf p P T) t := by
  set b := bOf p P T with hb
  have ha := hopt.1
  have has := astar_admissible p.r b T hp.hr
  have h1 := hopt.2 _ has
  rw [agentPay_per p T P _ has, agentPay_per p T P a ha] at h1
  have hd := one_sub_exp_pos hp.hr hT
  have h2 : ∫ t in (0:ℝ)..T, phiA p T P t (a t) ≤
      ∫ t in (0:ℝ)..T, phiA p T P t (astar p.r b T t) := by
    have := (div_le_div_iff_of_pos_right hd).1 h1; linarith
  have h3 : ∫ t in (0:ℝ)..T, phiA p T P t (astar p.r b T t) =
      ∫ t in (0:ℝ)..T, phiA p T P t (mb p.r b t) :=
    intervalIntegral.integral_congr fun t ht => by
      rw [uIcc_of_le hT.le] at ht; simp only [astar_eq ht.2]
  have hint_a := phiA_int p T P a ha
  have hint_m : IntervalIntegrable (fun t => phiA p T P t (mb p.r b t)) volume 0 T := by
    have := mb_cont1 p.r b
    unfold phiA
    exact Continuous.intervalIntegrable (by fun_prop) _ _
  have hnn : ∀ t ∈ Icc (0:ℝ) T, 0 ≤ phiA p T P t (a t) - phiA p T P t (mb p.r b t) :=
    fun t ht => by
      have := (pt_min_per p hp hP ht.1 ht.2 (ha.2.1 t)).1
      linarith
  have hzero : ∫ t in (0:ℝ)..T, (phiA p T P t (a t) - phiA p T P t (mb p.r b t)) = 0 := by
    have h4 := intervalIntegral.integral_nonneg (μ := volume) hT.le hnn
    rw [intervalIntegral.integral_sub hint_a hint_m] at h4 ⊢
    linarith
  rw [intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae hT.le ?_ (hint_a.sub hint_m)]
    at hzero
  · rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc] at hzero
    filter_upwards [hzero] with t ht htm
    have hz := ht htm
    simp only [Pi.zero_apply] at hz
    exact (pt_min_per p hp hP htm.1.le htm.2 (ha.2.1 t)).2 (by linarith)
  · rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall fun t ht => hnn t ⟨ht.1.le, ht.2⟩

lemma agentOpt_astar (p : Params) (hp : Standing p) {T : ℝ} (hT : 0 < T) (b : ℝ) :
    AgentOptimal p (Measure.dirac T) (p.c * Real.exp (b + p.r * T) / p.lam) (astar p.r b T) := by
  set P := p.c * Real.exp (b + p.r * T) / p.lam with hPdef
  have hc := hp.hc; have hl := hp.hlam
  have hP : 0 < P := by positivity
  have hbP : bOf p P T = b := by
    rw [bOf, if_pos hP, show P * p.lam / p.c = Real.exp (b + p.r * T) by
      rw [hPdef]; field_simp, Real.log_exp]
    ring
  have has := astar_admissible p.r b T hp.hr
  refine ⟨has, fun a' ha' => ?_⟩
  rw [agentPay_per p T P _ ha', agentPay_per p T P _ has]
  refine div_le_div_of_nonneg_right (neg_le_neg ?_) (one_sub_exp_pos hp.hr hT).le
  refine intervalIntegral.integral_mono_on hT.le (phiA_int p T P _ has) (phiA_int p T P a' ha')
    fun t ht => ?_
  rw [astar_eq ht.2]
  have := (pt_min_per p hp hP.le ht.1 ht.2 (ha'.2.1 t)).1
  rw [hbP] at this
  exact this

lemma reduced_per (p : Params) (hp : Standing p) (K : ℝ) {v : ℝ} (hv : 0 < v) (a : Effort)
    (ha : Admissible a) (b : ℝ) (hae : ∀ᵐ t, t ∈ Ioc 0 (1 / v) → a t = mb p.r b t) :
    reducedPayoff p K v (Measure.dirac (1 / v)) a =
      mubar p / p.r - Gper p.r p.c (p.L * p.lam) K (1 / v) b := by
  set T := 1 / v with hTdef
  have hT : 0 < T := by positivity
  have h1 : ∫ t in (0:ℝ)..T, a t * Real.exp (-(p.r * t)) =
      ∫ t in (0:ℝ)..T, mb p.r b t * Real.exp (-(p.r * t)) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with t ht ht'
    rw [uIoc_of_le hT.le] at ht'
    rw [ht ht']
  have h2 : ∫ s in (0:ℝ)..T, Real.exp (-(a s)) *
      ((Real.exp (-(p.r * s)) - Real.exp (-(p.r * T))) / p.r) =
      ∫ s in (0:ℝ)..T, Real.exp (-(mb p.r b s)) *
      ((Real.exp (-(p.r * s)) - Real.exp (-(p.r * T))) / p.r) := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hae] with t ht ht'
    rw [uIoc_of_le hT.le] at ht'
    rw [ht ht']
  have hm := mb_cont1 p.r b
  have hN : Nper p.r p.c (p.L * p.lam) T b = ∫ t in (0:ℝ)..T,
      (p.c * (mb p.r b t * Real.exp (-(p.r * t))) + p.L * (p.lam * (Real.exp (-(mb p.r b t)) *
        ((Real.exp (-(p.r * t)) - Real.exp (-(p.r * T))) / p.r)))) := by
    unfold Nper
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  have hi1 : IntervalIntegrable (fun t => p.c * (mb p.r b t * Real.exp (-(p.r * t)))) volume 0 T :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hi2 : IntervalIntegrable (fun t => p.L * (p.lam * (Real.exp (-(mb p.r b t)) *
      ((Real.exp (-(p.r * t)) - Real.exp (-(p.r * T))) / p.r)))) volume 0 T :=
    Continuous.intervalIntegrable (by fun_prop) _ _
  have hN' : Nper p.r p.c (p.L * p.lam) T b =
      p.c * (∫ t in (0:ℝ)..T, mb p.r b t * Real.exp (-(p.r * t))) +
        p.L * (p.lam * ∫ t in (0:ℝ)..T, Real.exp (-(mb p.r b t)) *
          ((Real.exp (-(p.r * t)) - Real.exp (-(p.r * T))) / p.r)) := by
    rw [hN, intervalIntegral.integral_add hi1 hi2]
    simp only [intervalIntegral.integral_const_mul]
  unfold reducedPayoff Gper
  rw [effort_per, loss_per p hp hT a ha, discF_per, h1, h2, hN',
    show p.r / v = p.r * T by rw [hTdef]; ring]
  ring

lemma per_upper (p : Params) (hp : Standing p) (K x : ℝ) (hx : Achievable p K periodicLaw x) :
    ∃ T, 0 < T ∧ ∃ b, x ≤ mubar p / p.r - Gper p.r p.c (p.L * p.lam) K T b := by
  obtain ⟨v, P, w, a, hv, hP, hw, hopt, hpart, rfl⟩ := hx
  have hT : 0 < 1 / v := by positivity
  refine ⟨1 / v, hT, bOf p P (1 / v), ?_⟩
  have hδ : discF p (periodicLaw v) < 1 := by
    rw [periodicLaw, discF_per]; have := one_sub_exp_pos hp.hr hT; linarith
  refine (principal_le_reduced p K v _ a P w hδ hp.hr hpart).trans (le_of_eq ?_)
  exact reduced_per p hp K hv a hopt.1 _ (br_unique p hp hT hP a hopt)

lemma per_ach (p : Params) (hp : Standing p) (K : ℝ) {T : ℝ} (hT : 0 < T) (b : ℝ) :
    Achievable p K periodicLaw (mubar p / p.r - Gper p.r p.c (p.L * p.lam) K T b) := by
  have hv : 0 < 1 / T := by positivity
  have hlaw : periodicLaw (1 / T) = Measure.dirac T := by rw [periodicLaw, one_div_one_div]
  have hc := hp.hc; have hl := hp.hlam
  have hopt := agentOpt_astar p hp hT b
  have hP : 0 ≤ p.c * Real.exp (b + p.r * T) / p.lam := by positivity
  have has := astar_admissible p.r b T hp.hr
  rw [← hlaw] at hopt
  have hδ : discF p (periodicLaw (1 / T)) < 1 := by
    rw [hlaw, discF_per]; have := one_sub_exp_pos hp.hr hT; linarith
  have hach := achievable_reduced p hp K periodicLaw hv hP (astar p.r b T) hopt hδ
    (by rw [hlaw]; exact effortInt_nonneg p _ (dirac_Iic_zero hT) _ has)
    (by rw [hlaw]; exact penaltyInt_nonneg p hp _ (dirac_Iic_zero hT) _ has)
  have hred := reduced_per p hp K hv (astar p.r b T) has b
    (by rw [one_div_one_div]; exact Filter.Eventually.of_forall fun t ht => astar_eq ht.2)
  rw [one_div_one_div] at hred
  rw [hlaw, hred] at hach
  exact hach

/-- C1: the periodic optimum is attained. -/
theorem C1 (p : Params) (hp : Standing p) (K : ℝ) (hK : 0 < K) :
    ∃ xD, Achievable p K periodicLaw xD ∧ ∀ x, Achievable p K periodicLaw x → x ≤ xD := by
  have hM : p.r * p.c < p.L * p.lam := by
    have := hp.asm1a; rw [lt_div_iff₀ hp.hr, mul_comm] at this; exact this
  obtain ⟨Ts, hTs, bs, hmin⟩ := Gper_min hp.hr hp.hc hM hK
  refine ⟨_, per_ach p hp K hTs bs, fun x hx => ?_⟩
  obtain ⟨T, hT, b, hle⟩ := per_upper p hp K x hx
  have := hmin T hT b
  linarith

/-! ## Reduction -/

lemma hybridLaw_one_eq : hybridLaw 1 = periodicLaw := by
  funext v
  simp [hybridLaw, periodicLaw]

lemma hybridLaw_zero_eq : hybridLaw 0 = randomLaw := by
  funext v
  simp [hybridLaw, randomLaw, Measure.map_id']

lemma achievableHybrid_of_periodic (p : Params) (K x : ℝ)
    (h : Achievable p K periodicLaw x) : AchievableHybrid p K x :=
  ⟨1, zero_le_one, le_rfl, by rw [hybridLaw_one_eq]; exact h⟩

lemma achievableHybrid_of_random (p : Params) (K x : ℝ)
    (h : Achievable p K randomLaw x) : AchievableHybrid p K x :=
  ⟨0, le_rfl, zero_le_one, by rw [hybridLaw_zero_eq]; exact h⟩

/-- The reduction: periodic optimum exists (C1) and some hybrid payoff beats every random
payoff (C2) give Proposition 5. -/
theorem reduction (p : Params) (K : ℝ)
    (C1 : ∃ xD, Achievable p K periodicLaw xD ∧ ∀ x, Achievable p K periodicLaw x → x ≤ xD)
    (C2 : ∃ xH, AchievableHybrid p K xH ∧ ∀ xR, Achievable p K randomLaw xR → xR < xH) :
    ∃ xH, AchievableHybrid p K xH ∧
      (∀ xR, Achievable p K randomLaw xR → xR < xH) ∧
      (∀ xD, Achievable p K periodicLaw xD → xD ≤ xH) := by
  obtain ⟨xD, hD, hDmax⟩ := C1
  obtain ⟨xH, hH, hHR⟩ := C2
  by_cases hle : xD ≤ xH
  · exact ⟨xH, hH, hHR, fun x hx => (hDmax x hx).trans hle⟩
  · push_neg at hle
    exact ⟨xD, achievableHybrid_of_periodic p K xD hD,
      fun x hx => (hHR x hx).trans hle, hDmax⟩

end OpRiskInspection.Hybrid.P5

open OpRiskInspection.RandomVsPeriodic in
theorem solution (p : OpRiskInspection.RandomVsPeriodic.Params) (hp : OpRiskInspection.RandomVsPeriodic.Standing p) (K : ℝ) (hK : 0 < K) :
    ∃ xH, OpRiskInspection.RandomVsPeriodic.AchievableHybrid p K xH ∧
      (∀ xR, OpRiskInspection.RandomVsPeriodic.Achievable p K OpRiskInspection.RandomVsPeriodic.randomLaw xR → xR < xH) ∧
      (∀ xD, OpRiskInspection.RandomVsPeriodic.Achievable p K OpRiskInspection.RandomVsPeriodic.periodicLaw xD → xD ≤ xH) := by
  exact OpRiskInspection.Hybrid.P5.reduction p K (OpRiskInspection.Hybrid.P5.C1 p hp K hK)
    (OpRiskInspection.Hybrid.P5.C2 p hp K hK)
