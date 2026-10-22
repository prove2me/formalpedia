-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P07.bernstein_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T22:00:31.255873+00:00
-- url     : https://prove2.me/submissions/157c8763-566b-4148-8dd2-274791f5f816

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P07
noncomputable section

open Set Filter MeasureTheory

open scoped Topology NNReal

open QAlgorithms.Papers.Independent.Gap48.P07

open QAlgorithms.Papers.Independent.Next46.P06

open QAlgorithms.Papers.Independent.Claimed50.P05 (graphDomain GraphCore graphPower)

open QAlgorithms.Papers.Independent.Renew46.P11
  (LaplaceImage Bernstein CompletelyMonotone SpecialBernstein StieltjesClass PositiveReal)

attribute [local instance] Classical.propDecidable

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- PDF p.9, Lemma 2.5: neither positivity nor uniqueness of summands is asserted. -/

theorem g73n_norm_one_sub_exp_neg_le (w : ℂ) (hw : 0 ≤ w.re) : ‖1 - Complex.exp (-w)‖ ≤ ‖w‖ := by
  have hE1 : Real.exp (-w.re) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hE0 : 0 < Real.exp (-w.re) := Real.exp_pos _
  have hE2 : 1 - w.re ≤ Real.exp (-w.re) := by have := Real.add_one_le_exp (-w.re); linarith
  have hc1 : Real.cos w.im ≤ 1 := Real.cos_le_one _
  have hc2 : 1 - w.im ^ 2 / 2 ≤ Real.cos w.im := Real.one_sub_sq_div_two_le_cos
  have hsc : Real.sin w.im ^ 2 + Real.cos w.im ^ 2 = 1 := Real.sin_sq_add_cos_sq _
  have key : ‖1 - Complex.exp (-w)‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.one_re, Complex.exp_re, Complex.neg_re, Complex.neg_im,
      Complex.sub_im, Complex.one_im, Complex.exp_im, Real.cos_neg, Real.sin_neg]
    set E := Real.exp (-w.re)
    set c := Real.cos w.im
    set sn := Real.sin w.im
    have e1 : (1 - E * c) * (1 - E * c) + (0 - E * -sn) * (0 - E * -sn) = (1 - E) ^ 2 + 2 * E * (1 - c) := by
      linear_combination E ^ 2 * hsc
    rw [e1]
    have f1 : (1 - E) ^ 2 ≤ w.re ^ 2 := by nlinarith
    have f2 : 2 * E * (1 - c) ≤ 2 * (1 - c) := by nlinarith
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp key

theorem g73n_norm_one_sub_exp_neg_le_two (w : ℂ) (hw : 0 ≤ w.re) : ‖1 - Complex.exp (-w)‖ ≤ 2 := by
  have : ‖Complex.exp (-w)‖ ≤ 1 := by
    rw [Complex.norm_exp]; exact Real.exp_le_one_iff.mpr (by simp; linarith)
  calc ‖1 - Complex.exp (-w)‖ ≤ ‖(1:ℂ)‖ + ‖Complex.exp (-w)‖ := norm_sub_le _ _
    _ ≤ 2 := by simp at this ⊢; linarith

theorem g73n_mul_exp_neg_le (u : ℝ) : u * Real.exp (-u) ≤ 1 - Real.exp (-u) := by
  have h := Real.add_one_le_exp u
  have h2 : Real.exp u * Real.exp (-u) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos (-u)]

theorem g73n_mul_exp_neg_le_one (u : ℝ) : u * Real.exp (-u) ≤ 1 := by
  have := g73n_mul_exp_neg_le u; linarith [Real.exp_pos (-u)]

/-- lower pointwise bound -/
theorem g73n_lower_pt (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (z : ℂ) (hz : 0 ≤ z.re) :
    (t * z.re) * Real.exp (-(t * z.re)) * min (s / t) 1 ≤ (1 - Complex.exp (-(s : ℂ) * z)).re := by
  have hre : (1 - Complex.exp (-(s : ℂ) * z)).re ≥ 1 - Real.exp (-(s * z.re)) := by
    simp only [Complex.sub_re, Complex.one_re, Complex.exp_re]
    have : (-(s:ℂ) * z).re = -(s * z.re) := by simp
    rw [this]
    nlinarith [Real.exp_pos (-(s * z.re)), Real.cos_le_one (-(s:ℂ) * z).im]
  refine le_trans ?_ hre
  rcases le_or_gt s t with hst | hst
  · rw [min_eq_left ((div_le_one ht).mpr hst)]
    have e1 : Real.exp (-(t * z.re)) ≤ Real.exp (-(s * z.re)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have := g73n_mul_exp_neg_le (s * z.re)
    have h3 : t * z.re * Real.exp (-(t * z.re)) * (s / t) = (s * z.re) * Real.exp (-(t * z.re)) := by
      field_simp
    rw [h3]
    nlinarith [mul_nonneg hs.le hz]
  · rw [min_eq_right ((one_le_div ht).mpr hst.le)]
    have e1 : Real.exp (-(s * z.re)) ≤ Real.exp (-(t * z.re)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have := g73n_mul_exp_neg_le (t * z.re)
    linarith

theorem g73n_upper_pt (s t : ℝ) (hs : 0 < s) (ht : 0 < t) (z : ℂ) (hz : 0 ≤ z.re) :
    ‖1 - Complex.exp (-(s : ℂ) * z)‖ ≤ max 2 (t * ‖z‖) * min (s / t) 1 := by
  have hw : 0 ≤ ((s : ℂ) * z).re := by simp; positivity
  have h1 := g73n_norm_one_sub_exp_neg_le ((s : ℂ) * z) hw
  have h2 := g73n_norm_one_sub_exp_neg_le_two ((s : ℂ) * z) hw
  rw [neg_mul]
  rcases le_or_gt s t with hst | hst
  · rw [min_eq_left ((div_le_one ht).mpr hst)]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le] at h1
    calc _ ≤ s * ‖z‖ := h1
      _ = (t * ‖z‖) * (s / t) := by field_simp
      _ ≤ _ := by gcongr; exact le_max_right _ _
  · rw [min_eq_right ((one_le_div ht).mpr hst.le)]
    linarith [le_max_left 2 (t * ‖z‖)]

theorem g73n_min_le (s : ℝ) (hs : 0 < s) : min s 1 ≤ 2 * (s / (1 + s)) := by
  rw [mul_div_assoc', le_div_iff₀ (by linarith)]
  rcases le_or_gt s 1 with h | h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h.le]; linarith


theorem g73n_ae_pos (g : BernsteinData) : ∀ᵐ s ∂g.mu, 0 < s := by
  rw [ae_iff]
  have : {a : ℝ | ¬ 0 < a} = Iic 0 := by ext; simp
  rw [this]; exact g.support_positive

theorem g73n_Ioi_one_fin (g : BernsteinData) : g.mu (Ioi 1) < ⊤ := by
  have h := g.levy_integrable.measure_norm_ge_lt_top (ε := 1/2) (by norm_num)
  refine lt_of_le_of_lt (measure_mono ?_) h
  intro s hs
  simp only [mem_Ioi] at hs
  simp only [mem_ofPred_eq, Real.norm_eq_abs]
  rw [abs_of_pos (by positivity), le_div_iff₀ (by linarith)]
  linarith

instance g73n_inst1 (g : BernsteinData) : IsFiniteMeasure (g.mu.restrict (Ioi 1)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact g73n_Ioi_one_fin g⟩

def g73n_mu1 (g : BernsteinData) : Measure ℝ≥0 :=
  Measure.dirac 0 + (g.mu.restrict (Ioi 1)).map Real.toNNReal

def g73n_h1 (g : BernsteinData) : ℝ≥0 → ℂ :=
  fun s => if s = 0 then ((g.a + g.mu.real (Ioi 1) : ℝ) : ℂ) else -1

instance g73n_inst2 (g : BernsteinData) : IsFiniteMeasure (g73n_mu1 g) := by
  unfold g73n_mu1; infer_instance

theorem g73n_h1_meas (g : BernsteinData) : Measurable (g73n_h1 g) :=
  Measurable.ite (measurableSet_singleton 0) measurable_const measurable_const

theorem g73n_h1_bd (g : BernsteinData) (s : ℝ≥0) : ‖g73n_h1 g s‖ ≤ |g.a + g.mu.real (Ioi 1)| + 1 := by
  unfold g73n_h1; split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs]; linarith
  · simp

theorem g73n_exp_bd (z : ℂ) (hz : 0 ≤ z.re) (s : ℝ) (hs : 0 ≤ s) :
    ‖Complex.exp (-(s : ℂ) * z)‖ ≤ 1 := by
  rw [Complex.norm_exp]; apply Real.exp_le_one_iff.mpr
  simp; positivity

theorem g73n_laplace_int {mu : Measure ℝ≥0} [IsFiniteMeasure mu] {h : ℝ≥0 → ℂ} (hm : Measurable h)
    (B : ℝ) (hB : ∀ s, ‖h s‖ ≤ B) (z : ℂ) (hz : 0 ≤ z.re) :
    Integrable (fun t : ℝ≥0 => Complex.exp (-((t : ℝ) : ℂ) * z) * h t) mu := by
  refine Integrable.of_bound ?_ B (Eventually.of_forall fun s => ?_)
  · exact ((by fun_prop : Continuous fun t : ℝ≥0 => Complex.exp (-((t : ℝ) : ℂ) * z)).measurable.mul
      hm).aestronglyMeasurable
  · rw [norm_mul]
    calc _ ≤ 1 * B := mul_le_mul (g73n_exp_bd z hz _ s.2) (hB s) (norm_nonneg _) zero_le_one
      _ = B := one_mul B

theorem g73n_g1_eval (g : BernsteinData) (z : ℂ) (hz : 0 ≤ z.re) :
    ∫ t : ℝ≥0, Complex.exp (-((t : ℝ) : ℂ) * z) * g73n_h1 g t ∂(g73n_mu1 g) =
      ((g.a + g.mu.real (Ioi 1) : ℝ) : ℂ) - ∫ s in Ioi 1, Complex.exp (-(s : ℂ) * z) ∂g.mu := by
  have hI := g73n_laplace_int (mu := g73n_mu1 g) (g73n_h1_meas g) _ (g73n_h1_bd g) z hz
  unfold g73n_mu1 at hI ⊢
  rw [integral_add_measure (hI.mono_measure (Measure.le_add_right le_rfl)) (hI.mono_measure (Measure.le_add_left le_rfl))]
  rw [integral_dirac, integral_map (by fun_prop) (hI.mono_measure (Measure.le_add_left le_rfl)).aestronglyMeasurable]
  · rw [setIntegral_congr_fun (g := fun s : ℝ => -Complex.exp (-(s : ℂ) * z)) measurableSet_Ioi]
    · rw [integral_neg]; simp [g73n_h1]; ring
    · intro s hs
      simp only [mem_Ioi] at hs
      have : Real.toNNReal s ≠ 0 := by simp; linarith
      simp only [g73n_h1, this, if_false, Real.coe_toNNReal _ (by linarith : (0:ℝ) ≤ s)]
      ring

theorem g73n_int_exp (g : BernsteinData) (z : ℂ) (hz : 0 ≤ z.re) :
    Integrable (fun s : ℝ => 1 - Complex.exp (-(s : ℂ) * z)) g.mu := by
  refine Integrable.mono' (g.levy_integrable.const_mul (2 * (2 + ‖z‖))) ?_ ?_
  · exact (by fun_prop : Continuous fun s : ℝ => 1 - Complex.exp (-(s : ℂ) * z)).aestronglyMeasurable
  · filter_upwards [g73n_ae_pos g] with s hs
    have h1 := g73n_upper_pt s 1 hs one_pos z hz
    have h2 := g73n_min_le s hs
    simp only [div_one, one_mul] at h1
    have h3 : max 2 ‖z‖ ≤ 2 + ‖z‖ := max_le (by linarith [norm_nonneg z]) (by linarith)
    have h4 : 0 ≤ min s 1 := le_min hs.le zero_le_one
    calc _ ≤ max 2 ‖z‖ * min s 1 := h1
      _ ≤ (2 + ‖z‖) * (2 * (s / (1 + s))) := by
        apply mul_le_mul h3 h2 h4; positivity
      _ = _ := by ring


theorem g73n_id_int (g : BernsteinData) : Integrable (fun s : ℝ => s) (g.mu.restrict (Ioc 0 1)) := by
  refine Integrable.mono' (g.levy_integrable.restrict.const_mul 2)
    (by fun_prop : Continuous fun s : ℝ => s).aestronglyMeasurable ?_
  rw [ae_restrict_iff' measurableSet_Ioc]
  refine Eventually.of_forall fun s hs => ?_
  obtain ⟨h0, h1⟩ := hs
  rw [Real.norm_eq_abs, abs_of_pos h0, mul_div_assoc', le_div_iff₀ (by linarith)]
  nlinarith

def g73n_nu (g : BernsteinData) : Measure ℝ :=
  (g.mu.restrict (Ioc 0 1)).withDensity (fun s => ENNReal.ofReal s)

instance g73n_inst3 (g : BernsteinData) : IsFiniteMeasure (g73n_nu g) :=
  isFiniteMeasure_withDensity_ofReal (g73n_id_int g).2

def g73n_mu2 (g : BernsteinData) : Measure ℝ≥0 :=
  ENNReal.ofReal g.b • Measure.dirac 0 +
    ((g73n_nu g).prod (volume.restrict (Icc (0:ℝ) 1))).map (fun p : ℝ × ℝ => Real.toNNReal (p.2 * p.1))

instance g73n_inst5 (b : ℝ) : IsFiniteMeasure (ENNReal.ofReal b • Measure.dirac (0 : ℝ≥0)) :=
  ⟨by simp⟩

instance g73n_inst4 (g : BernsteinData) : IsFiniteMeasure (g73n_mu2 g) := by
  unfold g73n_mu2; infer_instance

theorem g73n_g2_eval (g : BernsteinData) (z : ℂ) (hz : 0 ≤ z.re) (hz0 : z ≠ 0) :
    ∫ t : ℝ≥0, Complex.exp (-((t : ℝ) : ℂ) * z) * (fun _ => (1 : ℂ)) t ∂(g73n_mu2 g) =
      (g.b : ℂ) + ∫ s in Ioc 0 1, (1 - Complex.exp (-(s : ℂ) * z)) / z ∂g.mu := by
  have hcont : Continuous fun t : ℝ≥0 => Complex.exp (-((t : ℝ) : ℂ) * z) * (fun _ => (1 : ℂ)) t := by
    fun_prop
  have hI : Integrable (fun t : ℝ≥0 => Complex.exp (-((t : ℝ) : ℂ) * z) * (fun _ => (1 : ℂ)) t)
      (g73n_mu2 g) := by
    refine Integrable.of_bound hcont.aestronglyMeasurable 1 (Eventually.of_forall fun s => ?_)
    simpa using g73n_exp_bd z hz _ s.2
  have hφ : Measurable (fun p : ℝ × ℝ => Real.toNNReal (p.2 * p.1)) := by fun_prop
  unfold g73n_mu2 at hI ⊢
  rw [integral_add_measure (hI.mono_measure (Measure.le_add_right le_rfl))
    (hI.mono_measure (Measure.le_add_left le_rfl))]
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal g.b_nonneg,
    integral_map hφ.aemeasurable hcont.aestronglyMeasurable]
  have hP : Integrable ((fun t : ℝ≥0 => Complex.exp (-((t : ℝ) : ℂ) * z) * (fun _ => (1 : ℂ)) t) ∘
      (fun p : ℝ × ℝ => Real.toNNReal (p.2 * p.1))) ((g73n_nu g).prod (volume.restrict (Icc (0:ℝ) 1))) := by
    refine Integrable.of_bound (hcont.measurable.comp hφ).aestronglyMeasurable 1
      (Eventually.of_forall fun s => ?_)
    simpa using g73n_exp_bd z hz _ (Real.toNNReal _).2
  have hP' : Integrable (fun x : ℝ × ℝ => Complex.exp (-(((x.2 * x.1).toNNReal : ℝ) : ℂ) * z) *
      (fun _ => (1 : ℂ)) (x.2 * x.1).toNNReal) ((g73n_nu g).prod (volume.restrict (Icc (0:ℝ) 1))) := hP
  congr 1
  · simp
  rw [integral_prod _ hP']
  unfold g73n_nu
  have hd : (fun s : ℝ => ENNReal.ofReal s) = fun s => ((Real.toNNReal s : ℝ≥0) : ENNReal) := rfl
  rw [hd, integral_withDensity_eq_integral_smul measurable_real_toNNReal]
  refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
  obtain ⟨hs0, hs1⟩ := hs
  simp only [Function.comp, mul_one]
  have hc : (-(s : ℂ) * z) ≠ 0 := by
    have : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
    exact mul_ne_zero (neg_ne_zero.mpr this) hz0
  have hin : ∫ u in Icc (0:ℝ) 1, Complex.exp (-(((Real.toNNReal (u * s) : ℝ≥0) : ℝ) : ℂ) * z) =
      intervalIntegral (fun u : ℝ => Complex.exp ((-(s : ℂ) * z) * u)) 0 1 volume := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
    refine setIntegral_congr_fun measurableSet_Icc fun u hu => ?_
    rw [Real.coe_toNNReal _ (mul_nonneg hu.1 hs0.le)]
    congr 1; push_cast; ring
  rw [hin, integral_exp_mul_complex hc, NNReal.smul_def, Real.coe_toNNReal _ hs0.le]
  simp only [Complex.real_smul, Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero,
    Complex.exp_zero]
  have : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  field_simp
  ring

theorem solution (g : BernsteinData) :
    ∃ g1 g2 : ℂ → ℂ, LaplaceImage g1 ∧ LaplaceImage g2 ∧ ∀ z : ℝ, 0 < z →
      bernsteinValue g (z : ℂ) = g1 (z : ℂ) + (z : ℂ) * g2 (z : ℂ) := by
  refine ⟨fun z => ∫ t : ℝ≥0, Complex.exp (-((t : ℝ) : ℂ) * z) * g73n_h1 g t ∂(g73n_mu1 g),
    fun z => ∫ t : ℝ≥0, Complex.exp (-((t : ℝ) : ℂ) * z) * (fun _ => (1 : ℂ)) t ∂(g73n_mu2 g),
    ?_, ?_, ?_⟩
  · refine ⟨g73n_mu1 g, g73n_h1 g, inferInstance,
      Integrable.of_bound (g73n_h1_meas g).aestronglyMeasurable _
        (Eventually.of_forall (g73n_h1_bd g)), fun z hz => ⟨?_, rfl⟩⟩
    exact g73n_laplace_int (g73n_h1_meas g) _ (g73n_h1_bd g) z hz.le
  · refine ⟨g73n_mu2 g, fun _ => (1 : ℂ), inferInstance, integrable_const _, fun z hz => ⟨?_, rfl⟩⟩
    exact g73n_laplace_int measurable_const 1 (fun _ => by simp) z hz.le
  · intro x hx
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    have hxre : 0 ≤ (x : ℂ).re := by simp; exact hx.le
    simp only
    rw [g73n_g1_eval g _ hxre, g73n_g2_eval g _ hxre hx0]
    unfold bernsteinValue
    have hI := g73n_int_exp g (x : ℂ) hxre
    have hsplit : ∫ s, (1 - Complex.exp (-(s : ℂ) * x)) ∂g.mu =
        (∫ s in Ioc 0 1, (1 - Complex.exp (-(s : ℂ) * x)) ∂g.mu) +
          ∫ s in Ioi 1, (1 - Complex.exp (-(s : ℂ) * x)) ∂g.mu := by
      have hr : g.mu.restrict (Ioi 0) = g.mu := Measure.restrict_eq_self_of_ae_mem (g73n_ae_pos g)
      conv_lhs => rw [← hr]
      rw [← Ioc_union_Ioi_eq_Ioi zero_le_one,
        setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hI.integrableOn hI.integrableOn]
    have he : IntegrableOn (fun s : ℝ => Complex.exp (-(s : ℂ) * x)) (Ioi 1) g.mu := by
      refine Integrable.of_bound (by fun_prop : Continuous fun s : ℝ =>
        Complex.exp (-(s : ℂ) * x)).aestronglyMeasurable 1 ?_
      rw [ae_restrict_iff' measurableSet_Ioi]
      exact Eventually.of_forall fun s hs => g73n_exp_bd _ hxre s (by simp at hs; linarith)
    have h2 : ∫ s in Ioi 1, (1 - Complex.exp (-(s : ℂ) * x)) ∂g.mu =
        (g.mu.real (Ioi 1) : ℂ) - ∫ s in Ioi 1, Complex.exp (-(s : ℂ) * x) ∂g.mu := by
      rw [integral_sub (integrable_const 1) he, setIntegral_const]
      simp
    have h3 : ∫ s in Ioc 0 1, (1 - Complex.exp (-(s : ℂ) * x)) / (x : ℂ) ∂g.mu =
        (∫ s in Ioc 0 1, (1 - Complex.exp (-(s : ℂ) * x)) ∂g.mu) / (x : ℂ) := integral_div _ _
    rw [hsplit, h2, h3]
    push_cast
    field_simp
    ring


end
