-- Prove2me | solution 1 for TightReleaseSchedules.Stationary.Supplement.tracking_floor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-19T17:34:58.156538+00:00
-- url     : https://prove2.me/submissions/914640b9-7ca9-4064-85d0-032d8154892a

import Definitions.Def_TightReleaseSchedules_Stationary_Supplement_drift_class

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary

noncomputable section

namespace TRS.Dev.TrackingFloor

lemma pdf_shift (m ε : ℝ) :
    gaussianPDF m 1 ε = gaussianPDF 0 1 ε * ENNReal.ofReal (Real.exp (ε * m - m ^ 2 / 2)) := by
  unfold gaussianPDF gaussianPDFReal
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp only [NNReal.coe_one, mul_one]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

lemma gauss_shift_lintegral (m : ℝ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ ε, F (ε + m) ∂(gaussianReal 0 1) =
      ∫⁻ ε, F ε * ENNReal.ofReal (Real.exp (ε * m - m ^ 2 / 2)) ∂(gaussianReal 0 1) := by
  have h1 : ∫⁻ ε, F (ε + m) ∂(gaussianReal 0 1) = ∫⁻ ε, F ε ∂(gaussianReal m 1) := by
    have := gaussianReal_map_add_const (μ := 0) (v := 1) m
    rw [zero_add] at this
    rw [← this, lintegral_map hF (measurable_add_const m)]
  rw [h1, gaussianReal_of_var_ne_zero _ one_ne_zero, gaussianReal_of_var_ne_zero _ one_ne_zero,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_gaussianPDF _ _) hF,
    lintegral_withDensity_eq_lintegral_mul (g := fun ε => F ε * ENNReal.ofReal (Real.exp (ε * m - m ^ 2 / 2)))
      _ (measurable_gaussianPDF _ _) (hF.mul (by fun_prop))]
  refine lintegral_congr fun ε => ?_
  simp only [Pi.mul_apply]
  rw [pdf_shift]; ring

abbrev Row (d : ℕ) := Vector d × ℝ

def rowMeasure (d : ℕ) : Measure (Row d) := (stdGaussian (Vector d)).prod (gaussianReal 0 1)

instance (d : ℕ) : IsProbabilityMeasure (rowMeasure d) := by
  unfold rowMeasure; infer_instance

def rowShear {d : ℕ} (e : Vector d) (r : Row d) : Row d := (r.1, r.2 + inner ℝ r.1 e)

def rowD {d : ℕ} (e : Vector d) (r : Row d) : ℝ :=
  Real.exp (r.2 * inner ℝ r.1 e - (inner ℝ r.1 e) ^ 2 / 2)

lemma measurable_rowShear {d : ℕ} (e : Vector d) : Measurable (rowShear e) := by
  unfold rowShear; fun_prop

lemma measurable_rowD {d : ℕ} (e : Vector d) : Measurable (rowD e) := by
  unfold rowD; fun_prop

lemma row_shear_lintegral {d : ℕ} (e : Vector d) (F : Row d → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ r, F (rowShear e r) ∂(rowMeasure d) =
      ∫⁻ r, F r * ENNReal.ofReal (rowD e r) ∂(rowMeasure d) := by
  unfold rowMeasure
  rw [lintegral_prod (fun r : Row d => F (rowShear e r)) ((hF.comp (measurable_rowShear e)).aemeasurable),
    lintegral_prod (fun r : Row d => F r * ENNReal.ofReal (rowD e r))
      ((hF.mul (measurable_rowD e).ennreal_ofReal).aemeasurable)]
  refine lintegral_congr fun x => ?_
  have := gauss_shift_lintegral (inner ℝ x e) (fun ε => F (x, ε)) (hF.comp measurable_prodMk_left)
  simpa [rowShear, rowD] using this

lemma row_shear_map {d : ℕ} (e : Vector d) :
    (rowMeasure d).map (rowShear e) =
      (rowMeasure d).withDensity (fun r => ENNReal.ofReal (rowD e r)) := by
  ext s hs
  rw [Measure.map_apply (measurable_rowShear e) hs, withDensity_apply _ hs,
    ← lintegral_indicator hs, ← lintegral_indicator_one (measurable_rowShear e hs)]
  have := row_shear_lintegral e (s.indicator 1) (measurable_one.indicator hs)
  have h2 : ∫⁻ a, (rowShear e ⁻¹' s).indicator 1 a ∂rowMeasure d =
      ∫⁻ r, s.indicator 1 (rowShear e r) ∂rowMeasure d := by
    refine lintegral_congr fun r => ?_
    by_cases h : rowShear e r ∈ s <;> simp [h, Set.indicator]
  rw [h2, this]
  refine lintegral_congr fun r => ?_
  by_cases h : r ∈ s <;> simp [h, Set.indicator]

lemma gauss_exp_sq (σ2 : ℝ≥0) (h : 2 * (σ2 : ℝ) < 1) :
    ∫ t, Real.exp (t ^ 2) ∂(gaussianReal 0 σ2) = 1 / Real.sqrt (1 - 2 * σ2) := by
  by_cases h0 : σ2 = 0
  · subst h0; simp [gaussianReal_zero_var]
  have hpos : (0 : ℝ) < σ2 := by positivity
  rw [integral_gaussianReal_eq_integral_smul h0]
  have hb : (0 : ℝ) < 1 / (2 * σ2) - 1 := by
    rw [sub_pos, lt_div_iff₀ (by positivity)]; linarith
  have : ∀ x : ℝ, gaussianPDFReal 0 σ2 x • Real.exp (x ^ 2) =
      (Real.sqrt (2 * Real.pi * σ2))⁻¹ * Real.exp (-(1 / (2 * σ2) - 1) * x ^ 2) := by
    intro x
    unfold gaussianPDFReal
    rw [smul_eq_mul, mul_assoc, ← Real.exp_add]
    congr 2
    field_simp
    ring
  simp_rw [this]
  rw [integral_const_mul, integral_gaussian]
  rw [← Real.sqrt_inv, ← Real.sqrt_mul (by positivity), one_div]
  congr 1
  field_simp
  have h1 : (1 - (σ2 : ℝ) * 2) ≠ 0 := by linarith
  ring_nf
  first | rfl | (rw [Real.sqrt_inv]) 

lemma eps_sq_lintegral (m : ℝ) :
    ∫⁻ ε, ENNReal.ofReal (Real.exp (ε * m - m ^ 2 / 2)) ^ 2 ∂(gaussianReal 0 1) =
      ENNReal.ofReal (Real.exp (m ^ 2)) := by
  have hint : Integrable (fun ε : ℝ => Real.exp (-(m ^ 2)) * Real.exp ((2 * m) * ε))
      (gaussianReal 0 1) := (integrable_exp_mul_gaussianReal (2 * m)).const_mul _
  have h1 : ∀ ε : ℝ, ENNReal.ofReal (Real.exp (ε * m - m ^ 2 / 2)) ^ 2 =
      ENNReal.ofReal (Real.exp (-(m ^ 2)) * Real.exp ((2 * m) * ε)) := by
    intro ε
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [h1]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun ε =>
    by positivity), integral_const_mul]
  congr 1
  have := congrFun (mgf_id_gaussianReal (μ := 0) (v := 1)) (2 * m)
  simp only [mgf, id] at this
  rw [this, ← Real.exp_add]
  congr 1
  simp; ring

lemma stdGaussian_inner_exp_sq {d : ℕ} (e : Vector d) (h : 2 * ‖e‖ ^ 2 < 1) :
    ∫ x, Real.exp (inner ℝ x e ^ 2) ∂(stdGaussian (Vector d)) = 1 / Real.sqrt (1 - 2 * ‖e‖ ^ 2) := by
  set L : StrongDual ℝ (Vector d) := innerSL ℝ e
  have hL : ∀ x, L x = inner ℝ x e := fun x => by simp [L, real_inner_comm]
  have hmap := IsGaussian.map_eq_gaussianReal (μ := stdGaussian (Vector d)) L
  rw [integral_strongDual_stdGaussian, variance_dual_stdGaussian] at hmap
  have hn : ‖L‖ = ‖e‖ := by simp [L]
  rw [hn] at hmap
  have hnn : ((‖e‖ ^ 2).toNNReal : ℝ) = ‖e‖ ^ 2 := Real.coe_toNNReal _ (by positivity)
  have := gauss_exp_sq (‖e‖ ^ 2).toNNReal (by rw [hnn]; exact h)
  rw [hnn] at this
  rw [← this, ← hmap, integral_map L.continuous.aemeasurable (by fun_prop)]
  simp [hL]

lemma pi_withDensity {ι : Type} [Fintype ι] {X : Type} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] (f : ι → X → ℝ) (hf : ∀ i, Measurable (f i))
    (hnn : ∀ i x, 0 ≤ f i x) (hint : ∀ i, Integrable (f i) ν) :
    (Measure.pi (fun _ : ι => ν)).withDensity (fun z => ENNReal.ofReal (∏ i, f i (z i))) =
      Measure.pi (fun i => ν.withDensity (fun x => ENNReal.ofReal (f i x))) := by
  refine (Measure.pi_eq fun s hs => ?_).symm
  have hbox : MeasurableSet (Set.univ.pi s) := MeasurableSet.univ_pi hs
  rw [withDensity_apply _ hbox]
  have h1 : ∀ z : ι → X, (Set.univ.pi s).indicator (fun z => ENNReal.ofReal (∏ i, f i (z i))) z =
      ENNReal.ofReal (∏ i, (s i).indicator (f i) (z i)) := by
    intro z
    by_cases hz : z ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hz]
      have : ∏ i, f i (z i) = ∏ i, (s i).indicator (f i) (z i) :=
        Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hz i (Set.mem_univ i)) _).symm
      rw [this]
    · rw [Set.indicator_of_notMem hz]
      have : ∃ i, z i ∉ s i := by
        by_contra hc
        push Not at hc
        exact hz fun i _ => hc i
      obtain ⟨i, hi⟩ := this
      have : ∏ i, (s i).indicator (f i) (z i) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)
      rw [this]; simp
  rw [← lintegral_indicator hbox]
  simp_rw [h1]
  have hint2 : ∀ i, Integrable ((s i).indicator (f i)) ν := fun i => (hint i).indicator (hs i)
  have hnn2 : ∀ i x, 0 ≤ (s i).indicator (f i) x := fun i x =>
    Set.indicator_nonneg (fun y _ => hnn i y) x
  rw [← ofReal_integral_eq_lintegral_ofReal
    (Integrable.fintype_prod (f := fun i x => (s i).indicator (f i) x) hint2)
    (Filter.Eventually.of_forall fun z => Finset.prod_nonneg fun i _ => hnn2 i _),
    integral_fintype_prod_eq_prod (fun i x => (s i).indicator (f i) x),
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hnn2 i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i), integral_indicator (hs i),
    ofReal_integral_eq_lintegral_ofReal (hint i).restrict
    (Filter.Eventually.of_forall fun x => hnn i x)]

lemma rowD_lintegral {d : ℕ} (e : Vector d) :
    ∫⁻ r, ENNReal.ofReal (rowD e r) ∂(rowMeasure d) = 1 := by
  have := congrArg (fun m => m Set.univ) (row_shear_map e)
  simp only [Measure.map_apply (measurable_rowShear e) MeasurableSet.univ, Set.preimage_univ,
    measure_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
  exact this.symm

lemma rowD_integrable {d : ℕ} (e : Vector d) : Integrable (rowD e) (rowMeasure d) := by
  refine ⟨(measurable_rowD e).aestronglyMeasurable, ?_⟩
  have h : ∀ r, ‖rowD e r‖ₑ = ENNReal.ofReal (rowD e r) := fun r => by
    rw [Real.enorm_eq_ofReal (show 0 ≤ rowD e r from (Real.exp_pos _).le)]
  simp only [HasFiniteIntegral, h, rowD_lintegral]
  exact ENNReal.one_lt_top

lemma rowD_sq_lintegral {d : ℕ} (e : Vector d) (h : 2 * ‖e‖ ^ 2 < 1) :
    ∫⁻ r, ENNReal.ofReal (rowD e r ^ 2) ∂(rowMeasure d) =
      ENNReal.ofReal (1 / Real.sqrt (1 - 2 * ‖e‖ ^ 2)) := by
  have hpos : 0 < 1 / Real.sqrt (1 - 2 * ‖e‖ ^ 2) := by
    have : 0 < 1 - 2 * ‖e‖ ^ 2 := by linarith
    positivity
  have hint : Integrable (fun x : Vector d => Real.exp (inner ℝ x e ^ 2)) (stdGaussian (Vector d)) := by
    apply Integrable.of_integral_ne_zero
    rw [stdGaussian_inner_exp_sq e h]; exact hpos.ne'
  unfold rowMeasure
  rw [lintegral_prod (fun r : Row d => ENNReal.ofReal (rowD e r ^ 2))
    (((measurable_rowD e).pow_const 2).ennreal_ofReal.aemeasurable)]
  have h1 : ∀ x : Vector d, ∫⁻ ε, ENNReal.ofReal (rowD e (x, ε) ^ 2) ∂(gaussianReal 0 1) =
      ENNReal.ofReal (Real.exp (inner ℝ x e ^ 2)) := by
    intro x
    rw [← eps_sq_lintegral (inner ℝ x e)]
    refine lintegral_congr fun ε => ?_
    rw [← ENNReal.ofReal_pow (Real.exp_pos _).le]
    rfl
  simp_rw [h1]
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x =>
    (Real.exp_pos _).le), stdGaussian_inner_exp_sq e h]

lemma rowD_sq_integrable {d : ℕ} (e : Vector d) (h : 2 * ‖e‖ ^ 2 < 1) :
    Integrable (fun r => rowD e r ^ 2) (rowMeasure d) := by
  refine ⟨((measurable_rowD e).pow_const 2).aestronglyMeasurable, ?_⟩
  have h1 : ∀ r, ‖rowD e r ^ 2‖ₑ = ENNReal.ofReal (rowD e r ^ 2) := fun r => by
    rw [Real.enorm_eq_ofReal (show 0 ≤ rowD e r ^ 2 by positivity)]
  simp only [HasFiniteIntegral, h1, rowD_sq_lintegral e h]
  exact ENNReal.ofReal_lt_top

lemma rowD_sq_integral {d : ℕ} (e : Vector d) (h : 2 * ‖e‖ ^ 2 < 1) :
    ∫ r, rowD e r ^ 2 ∂(rowMeasure d) = 1 / Real.sqrt (1 - 2 * ‖e‖ ^ 2) := by
  have hpos : 0 < 1 / Real.sqrt (1 - 2 * ‖e‖ ^ 2) := by
    have : 0 < 1 - 2 * ‖e‖ ^ 2 := by linarith
    positivity
  have := rowD_sq_lintegral e h
  rw [← ofReal_integral_eq_lintegral_ofReal (rowD_sq_integrable e h)
    (Filter.Eventually.of_forall fun r => by positivity)] at this
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun r => by positivity) hpos.le).1 this

def shearG {T d : ℕ} (e : Fin T → Vector d) (z : GaussianRows T d) : GaussianRows T d :=
  fun i => rowShear (e i) (z i)

def densG {T d : ℕ} (e : Fin T → Vector d) (z : GaussianRows T d) : ℝ :=
  ∏ i, rowD (e i) (z i)

lemma measurable_shearG {T d : ℕ} (e : Fin T → Vector d) : Measurable (shearG e) :=
  measurable_pi_lambda _ fun i => (measurable_rowShear (e i)).comp (measurable_pi_apply i)

lemma measurable_densG {T d : ℕ} (e : Fin T → Vector d) : Measurable (densG e) :=
  Finset.measurable_prod _ fun i _ => (measurable_rowD (e i)).comp (measurable_pi_apply i)

lemma densG_nonneg {T d : ℕ} (e : Fin T → Vector d) (z : GaussianRows T d) : 0 ≤ densG e z :=
  Finset.prod_nonneg fun i _ => (Real.exp_pos _).le

lemma shearG_map {T d : ℕ} (e : Fin T → Vector d) :
    (gaussianRows T d).map (shearG e) =
      (gaussianRows T d).withDensity (fun z => ENNReal.ofReal (densG e z)) := by
  unfold gaussianRows
  have h1 : Measure.pi (fun _ : Fin T => (stdGaussian (Vector d)).prod (gaussianReal 0 1)) =
      Measure.pi (fun _ : Fin T => rowMeasure d) := rfl
  rw [h1]
  have h2 : shearG (T := T) e = fun z i => rowShear (e i) (z i) := rfl
  rw [h2]
  have : ∀ i : Fin T, SigmaFinite ((rowMeasure d).map (rowShear (e i))) := fun i => inferInstance
  rw [Measure.pi_map_pi (fun i => (measurable_rowShear (e i)).aemeasurable)]
  unfold densG
  rw [pi_withDensity (rowMeasure d) (fun i => rowD (e i)) (fun i => measurable_rowD (e i))
    (fun i r => (Real.exp_pos _).le) (fun i => rowD_integrable (e i))]
  congr 1
  funext i
  exact row_shear_map (e i)

lemma shearG_lintegral {T d : ℕ} (e : Fin T → Vector d) (F : GaussianRows T d → ℝ≥0∞)
    (hF : Measurable F) :
    ∫⁻ z, F (shearG e z) ∂(gaussianRows T d) =
      ∫⁻ z, ENNReal.ofReal (densG e z) * F z ∂(gaussianRows T d) := by
  rw [← lintegral_map hF (measurable_shearG e), shearG_map,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_densG e).ennreal_ofReal hF]
  rfl

lemma densG_sq_integral {T d : ℕ} (e : Fin T → Vector d) (h : ∀ i, 2 * ‖e i‖ ^ 2 < 1) :
    ∫ z, densG e z ^ 2 ∂(gaussianRows T d) =
      ∏ i, (1 / Real.sqrt (1 - 2 * ‖e i‖ ^ 2)) := by
  unfold densG gaussianRows
  have h1 : Measure.pi (fun _ : Fin T => (stdGaussian (Vector d)).prod (gaussianReal 0 1)) =
      Measure.pi (fun _ : Fin T => rowMeasure d) := rfl
  rw [h1]
  simp_rw [← Finset.prod_pow]
  rw [integral_fintype_prod_eq_prod (fun i (r : Row d) => rowD (e i) r ^ 2)]
  exact Finset.prod_congr rfl fun i _ => rowD_sq_integral (e i) (h i)

lemma densG_sq_lintegral {T d : ℕ} (e : Fin T → Vector d) (h : ∀ i, 2 * ‖e i‖ ^ 2 < 1) :
    ∫⁻ z, ENNReal.ofReal (densG e z) ^ 2 ∂(gaussianRows T d) =
      ENNReal.ofReal (∏ i, (1 / Real.sqrt (1 - 2 * ‖e i‖ ^ 2))) := by
  have hint : Integrable (fun z : GaussianRows T d => densG e z ^ 2) (gaussianRows T d) := by
    unfold densG gaussianRows
    have h1 : Measure.pi (fun _ : Fin T => (stdGaussian (Vector d)).prod (gaussianReal 0 1)) =
        Measure.pi (fun _ : Fin T => rowMeasure d) := rfl
    rw [h1]
    simp_rw [← Finset.prod_pow]
    exact Integrable.fintype_prod (f := fun i (r : Row d) => rowD (e i) r ^ 2)
      fun i => rowD_sq_integrable (e i) (h i)
  rw [← densG_sq_integral e h]
  rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun z => by positivity)]
  refine lintegral_congr fun z => ?_
  exact (ENNReal.ofReal_pow (densG_nonneg e z) 2).symm

end TRS.Dev.TrackingFloor

end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary

noncomputable section

namespace TRS.Dev.TrackingFloor

lemma obs_shear {T d : ℕ} (θ θ' : Fin T → Vector d) (z : GaussianRows T d) :
    observations θ' z = observations θ (shearG (fun i => θ' i - θ i) z) := by
  funext i
  simp only [observations, shearG, rowShear, inner_sub_right]
  congr 1
  ring

lemma measurable_observations {T d : ℕ} (θ : Fin T → Vector d) :
    Measurable (observations (T := T) (d := d) θ) := by
  refine measurable_pi_lambda _ fun i => ?_
  unfold observations
  have h1 : Measurable fun z : GaussianRows T d => (z i).1 :=
    measurable_fst.comp (measurable_pi_apply i)
  have h2 : Measurable fun z : GaussianRows T d => (z i).2 :=
    measurable_snd.comp (measurable_pi_apply i)
  exact h1.prodMk ((h1.inner measurable_const).add h2)

/-- Event: the test statistic `g` is `≤ 0` on the data generated by path `θ`. -/
def Ev {s : RandomSeed} {T d : ℕ} (g : s.space × Data T d → ℝ) (θ : Fin T → Vector d) :
    Set (s.space × GaussianRows T d) :=
  {ω | g (ω.1, observations θ ω.2) ≤ 0}

lemma measurableSet_Ev {s : RandomSeed} {T d : ℕ} (g : s.space × Data T d → ℝ)
    (hg : Measurable g) (θ : Fin T → Vector d) : MeasurableSet (Ev g θ) :=
  measurableSet_le (hg.comp (measurable_fst.prodMk
    ((measurable_observations θ).comp measurable_snd))) measurable_const

lemma two_point {s : RandomSeed} {T d : ℕ} (θ θ' : Fin T → Vector d)
    (g : s.space × Data T d → ℝ) (hg : Measurable g)
    (h : ∀ i, 2 * ‖θ' i - θ i‖ ^ 2 < 1) (χ : ℝ)
    (hχ : ∏ i, (1 / Real.sqrt (1 - 2 * ‖θ' i - θ i‖ ^ 2)) ≤ χ) :
    ((s.law.prod (gaussianRows T d)) (Ev g θ')).toReal ≤
      ((s.law.prod (gaussianRows T d)) (Ev g θ)).toReal + χ / 4 := by
  set e : Fin T → Vector d := fun i => θ' i - θ i with he
  set μ := s.law.prod (gaussianRows T d) with hμ
  have : IsProbabilityMeasure (gaussianRows T d) := by
    unfold gaussianRows; infer_instance
  have hEm := measurableSet_Ev g hg θ
  set χ0 : ℝ := ∏ i, (1 / Real.sqrt (1 - 2 * ‖e i‖ ^ 2)) with hχ0
  have hχ0pos : 0 ≤ χ0 :=
    Finset.prod_nonneg fun i _ => by positivity
  -- change of measure
  have hDm : Measurable fun ω : s.space × GaussianRows T d => ENNReal.ofReal (densG e ω.2) :=
    ((measurable_densG e).comp measurable_snd).ennreal_ofReal
  have hind : Measurable ((Ev g θ).indicator (1 : s.space × GaussianRows T d → ℝ≥0∞)) :=
    measurable_one.indicator hEm
  have hpre : ∀ σ z, (Ev g θ').indicator (1 : s.space × GaussianRows T d → ℝ≥0∞) (σ, z) =
      (Ev g θ).indicator (1 : s.space × GaussianRows T d → ℝ≥0∞) (σ, shearG e z) := by
    intro σ z
    have : ((σ, z) ∈ Ev g θ') ↔ ((σ, shearG e z) ∈ Ev g θ) := by
      simp only [Ev, Set.mem_setOf_eq, obs_shear θ θ' z]
      rfl
    by_cases hh : (σ, z) ∈ Ev g θ'
    · rw [Set.indicator_of_mem hh, Set.indicator_of_mem (this.1 hh)]; rfl
    · rw [Set.indicator_of_notMem hh, Set.indicator_of_notMem (fun h' => hh (this.2 h'))]
  have hshift : μ (Ev g θ') = ∫⁻ ω, ENNReal.ofReal (densG e ω.2) * (Ev g θ).indicator 1 ω ∂μ := by
    have hprod : Measurable fun ω : s.space × GaussianRows T d =>
        ENNReal.ofReal (densG e ω.2) * (Ev g θ).indicator 1 ω := hDm.mul hind
    rw [← lintegral_indicator_one (measurableSet_Ev g hg θ'), hμ,
      lintegral_prod _ (measurable_one.indicator (measurableSet_Ev g hg θ')).aemeasurable,
      lintegral_prod _ hprod.aemeasurable]
    refine lintegral_congr fun σ => ?_
    have hF : Measurable fun z : GaussianRows T d => (Ev g θ).indicator
        (1 : s.space × GaussianRows T d → ℝ≥0∞) (σ, z) := hind.comp measurable_prodMk_left
    simp_rw [hpre]
    rw [shearG_lintegral e _ hF]
  have hCS := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    hDm.aemeasurable hind.aemeasurable
  have e1 : ∫⁻ ω, ENNReal.ofReal (densG e ω.2) ^ (2 : ℝ) ∂μ = ENNReal.ofReal χ0 := by
    simp_rw [ENNReal.rpow_two]
    rw [hμ, lintegral_prod _ (hDm.pow_const 2).aemeasurable]
    simp only [lintegral_const, measure_univ, mul_one]
    exact densG_sq_lintegral e h
  have e2 : ∫⁻ ω, ((Ev g θ).indicator (1 : s.space × GaussianRows T d → ℝ≥0∞) ω) ^ (2 : ℝ) ∂μ
      = μ (Ev g θ) := by
    rw [← lintegral_indicator_one hEm]
    refine lintegral_congr fun a => ?_
    by_cases hh : a ∈ Ev g θ <;> simp [Set.indicator, hh]
  rw [e1, e2] at hCS
  have hCS' : μ (Ev g θ') ≤ _ := hshift ▸ hCS
  clear hCS
  -- square
  have hp : μ (Ev g θ) ≠ ⊤ := measure_ne_top _ _
  have hsq : (μ (Ev g θ')) ^ 2 ≤ ENNReal.ofReal χ0 * μ (Ev g θ) := by
    have h3 : μ (Ev g θ') ≤ (ENNReal.ofReal χ0 * μ (Ev g θ)) ^ (1 / (2 : ℝ)) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]; exact hCS'
    calc (μ (Ev g θ')) ^ 2 ≤ ((ENNReal.ofReal χ0 * μ (Ev g θ)) ^ (1 / (2 : ℝ))) ^ 2 := by gcongr
      _ = _ := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
  have hsq' : ((μ (Ev g θ')).toReal) ^ 2 ≤ χ0 * (μ (Ev g θ)).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hp) hsq
    rwa [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_ofReal hχ0pos] at this
  have hq0 := ENNReal.toReal_nonneg (a := μ (Ev g θ'))
  have hp0 := ENNReal.toReal_nonneg (a := μ (Ev g θ))
  set q := (μ (Ev g θ')).toReal
  set p := (μ (Ev g θ)).toReal
  have hχ' : χ0 ≤ χ := hχ
  by_contra hcon
  push Not at hcon
  have h5 : (p + χ / 4) ^ 2 < q ^ 2 := by
    apply pow_lt_pow_left₀ hcon (by
      have : 0 ≤ χ := hχ0pos.trans hχ'
      positivity) (by norm_num)
  nlinarith [sq_nonneg (p - χ / 4), mul_le_mul_of_nonneg_right hχ' hp0]

end TRS.Dev.TrackingFloor

end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement

noncomputable section

namespace TRS.Dev.TrackingFloor

/-! ## Tent profile and arithmetic of blocks -/

def hh (w : ℕ) (i : ℕ) : ℝ := 1 - |2 * (i : ℝ) - w| / w

lemma hh_succ (w : ℕ) (hw : 0 < w) (i : ℕ) : |hh w (i + 1) - hh w i| ≤ 2 / w := by
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  unfold hh
  have : 1 - |2 * ((i + 1 : ℕ) : ℝ) - w| / w - (1 - |2 * (i : ℝ) - w| / w) =
      (|2 * (i : ℝ) - w| - |2 * ((i + 1 : ℕ) : ℝ) - w|) / w := by ring
  rw [this, abs_div, abs_of_pos hw']
  apply div_le_div_of_nonneg_right _ hw'.le
  refine (abs_abs_sub_abs_le_abs_sub _ _).trans ?_
  push_cast
  rw [show 2 * (i : ℝ) - w - (2 * ((i : ℝ) + 1) - w) = -2 by ring]
  simp

lemma hh_one (w : ℕ) (hw : 2 ≤ w) : hh w 1 = 2 / w := by
  have hw' : (2 : ℝ) ≤ w := by exact_mod_cast hw
  unfold hh
  rw [show 2 * ((1 : ℕ) : ℝ) - w = -(w - 2) by push_cast; ring, abs_neg,
    abs_of_nonneg (by linarith)]
  field_simp
  ring

lemma hh_self (w : ℕ) (hw : 0 < w) : hh w w = 0 := by
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  unfold hh
  rw [show 2 * (w : ℝ) - w = w by ring, abs_of_pos hw']
  field_simp
  ring

lemma hh_nonneg (w i : ℕ) (hw : 0 < w) (hi : i ≤ w) : 0 ≤ hh w i := by
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  have hi' : (i : ℝ) ≤ w := by exact_mod_cast hi
  unfold hh
  have : |2 * (i : ℝ) - w| ≤ w := by
    rw [abs_le]; constructor <;> nlinarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  have : |2 * (i : ℝ) - w| / w ≤ 1 := by rw [div_le_one hw']; exact this
  linarith

lemma hh_le_one (w i : ℕ) (hw : 0 < w) : hh w i ≤ 1 := by
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  unfold hh
  have : 0 ≤ |2 * (i : ℝ) - w| / w := by positivity
  linarith

lemma hh_half (w p : ℕ) (hw : 0 < w) (h1 : (w + 3) / 4 ≤ p) (h2 : p ≤ 3 * w / 4) :
    1 / 2 ≤ hh w p := by
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw
  have a1 : (w : ℝ) ≤ 4 * p := by
    have : w ≤ 4 * p := by omega
    exact_mod_cast this
  have a2 : 4 * (p : ℝ) ≤ 3 * w := by
    have : 4 * p ≤ 3 * w := by omega
    exact_mod_cast this
  unfold hh
  have : |2 * (p : ℝ) - w| ≤ w / 2 := by
    rw [abs_le]; constructor <;> linarith
  have : |2 * (p : ℝ) - w| / w ≤ 1 / 2 := by
    rw [div_le_iff₀ hw']; linarith
  linarith

lemma blk_succ (w r : ℕ) (hw : 0 < w) (hr : 1 ≤ r) :
    ((r - 1) % w + 1 < w ∧ r / w = (r - 1) / w ∧ r % w = (r - 1) % w + 1) ∨
    ((r - 1) % w + 1 = w ∧ r / w = (r - 1) / w + 1) := by
  have hd := Nat.div_add_mod (r - 1) w
  have hm := Nat.mod_lt (r - 1) hw
  generalize (r - 1) / w = q at *
  generalize (r - 1) % w = m at *
  have hr' : r = w * q + m + 1 := by omega
  rcases Nat.lt_or_ge (m + 1) w with h | h
  · left
    refine ⟨h, ?_, ?_⟩
    · rw [hr']
      apply Nat.div_eq_of_lt_le <;> nlinarith
    · rw [hr']
      rw [Nat.add_assoc, Nat.mul_add_mod]
      exact Nat.mod_eq_of_lt h
  · right
    have : m + 1 = w := by omega
    refine ⟨this, ?_⟩
    rw [hr']
    apply Nat.div_eq_of_lt_le <;> nlinarith

lemma blk_pos (w q p : ℕ) (hp1 : 1 ≤ p) (hpw : p ≤ w) :
    (w * q + p - 1) / w = q ∧ (w * q + p - 1) % w = p - 1 := by
  have hw : 0 < w := by omega
  have : w * q + p - 1 = (p - 1) + w * q := by omega
  rw [this, Nat.add_mul_div_left _ _ hw, Nat.add_mul_mod_self_left]
  have : p - 1 < w := by omega
  rw [Nat.div_eq_of_lt this, Nat.mod_eq_of_lt this]
  simp


/-! ## Sign vectors and the path -/

def sgn (b : Bool) : ℝ := if b then 1 else -1

lemma sgn_sq (b : Bool) : sgn b ^ 2 = 1 := by cases b <;> simp [sgn]

/-- Unit sign vector of block `k`. -/
def sig (d K : ℕ) (u : Fin K × Fin d → Bool) (k : Fin K) : Vector d :=
  WithLp.toLp 2 (fun c : Fin d => sgn (u (k, c)) / Real.sqrt d)

def sigN (d K : ℕ) (u : Fin K × Fin d → Bool) (k : ℕ) : Vector d :=
  if h : k < K then sig d K u ⟨k, h⟩ else 0

lemma norm_sig (d K : ℕ) (hd : 0 < d) (u : Fin K × Fin d → Bool) (k : Fin K) :
    ‖sig d K u k‖ = 1 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : ‖sig d K u k‖ ^ 2 = 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [sig, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs, div_pow, sgn_sq,
      Real.sq_sqrt hd'.le, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have := norm_nonneg (sig d K u k)
  nlinarith

lemma norm_sigN_le (d K : ℕ) (hd : 0 < d) (u : Fin K × Fin d → Bool) (k : ℕ) :
    ‖sigN d K u k‖ ≤ 1 := by
  unfold sigN
  split_ifs with h
  · exact (norm_sig d K hd u _).le
  · simp

/-- Amplitude profile at (0-indexed) round `r`: round `0` and rounds past block `K` are at `θ₀`. -/
def amp (w K : ℕ) (A : ℝ) (r : ℕ) : ℝ :=
  if 1 ≤ r ∧ (r - 1) / w < K then A * hh w ((r - 1) % w + 1) else 0

def pathθ {T d : ℕ} (θ₀ : Vector d) (w K : ℕ) (A : ℝ) (u : Fin K × Fin d → Bool) :
    Fin T → Vector d :=
  fun r => θ₀ + amp w K A r.val • sigN d K u ((r.val - 1) / w)

lemma abs_amp_le (w K : ℕ) (A : ℝ) (hA : 0 ≤ A) (hw : 0 < w) (r : ℕ) :
    |amp w K A r| ≤ A := by
  unfold amp
  split_ifs
  · have h1 := hh_le_one w ((r - 1) % w + 1) hw
    have h2 := hh_nonneg w ((r - 1) % w + 1) hw (Nat.mod_lt _ hw)
    rw [abs_of_nonneg (mul_nonneg hA h2)]
    nlinarith
  · simpa using hA

lemma amp_nonneg (w K : ℕ) (A : ℝ) (hA : 0 ≤ A) (hw : 0 < w) (r : ℕ) : 0 ≤ amp w K A r := by
  unfold amp
  split_ifs
  · exact mul_nonneg hA (hh_nonneg w _ hw (Nat.mod_lt _ hw))
  · exact le_refl _

lemma amp_zero (w K : ℕ) (A : ℝ) : amp w K A 0 = 0 := by simp [amp]

lemma amp_one (w K : ℕ) (A : ℝ) (hw : 2 ≤ w) : |amp w K A 1| ≤ A * (2 / w) ∨ A < 0 := by
  by_cases hA : A < 0
  · right; exact hA
  left
  push Not at hA
  unfold amp
  split_ifs
  · simp only [Nat.sub_self, Nat.zero_div, Nat.zero_mod, zero_add]
    rw [hh_one w hw, abs_of_nonneg (by positivity)]
  · simp; positivity

lemma amp_diff (w K : ℕ) (A : ℝ) (hA : 0 ≤ A) (hw : 2 ≤ w) (r : ℕ) (hr : 1 ≤ r) :
    ((r - 1) % w + 1 < w → |amp w K A (r + 1) - amp w K A r| ≤ A * (2 / w)) ∧
    ((r - 1) % w + 1 = w → amp w K A r = 0 ∧ |amp w K A (r + 1)| ≤ A * (2 / w)) := by
  have hw0 : 0 < w := by omega
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw0
  rcases blk_succ w r hw0 hr with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
  · refine ⟨fun _ => ?_, fun h => by omega⟩
    unfold amp
    have e : r + 1 - 1 = r := by omega
    rw [e, h2, h3]
    by_cases hk : (r - 1) / w < K
    · rw [if_pos ⟨by omega, hk⟩, if_pos ⟨hr, hk⟩, ← mul_sub, abs_mul, abs_of_nonneg hA]
      exact mul_le_mul_of_nonneg_left (by simpa using hh_succ w hw0 ((r - 1) % w + 1)) hA
    · rw [if_neg (fun h => hk h.2), if_neg (fun h => hk h.2)]
      simp; positivity
  · refine ⟨fun h => by omega, fun _ => ?_⟩
    have hz : amp w K A r = 0 := by
      unfold amp
      split_ifs
      · rw [h1, hh_self w hw0]; simp
      · rfl
    refine ⟨hz, ?_⟩
    unfold amp
    have e : r + 1 - 1 = r := by omega
    rw [e, h2]
    split_ifs with hh1
    · have : r % w = 0 := by
        have hd := Nat.div_add_mod (r - 1) w
        have : r = w * ((r - 1) / w + 1) := by
          generalize (r - 1) / w = q at *
          generalize (r - 1) % w = m at *
          rw [mul_add, mul_one]; omega
        rw [this]; exact Nat.mul_mod_right _ _
      rw [this]
      simp only [zero_add]
      rw [hh_one w hw, abs_of_nonneg (by positivity)]
    · simp; positivity

lemma pathθ_mem {T d : ℕ} (θ₀ : Vector d) (hd : 0 < d) (w K : ℕ) (hw : 2 ≤ w) (η : ℝ)
    (hη : 0 ≤ η) (u : Fin K × Fin d → Bool) :
    pathθ (T := T) θ₀ w K (η * w / 2) u ∈ driftClass (T := T) θ₀ 0 η := by
  have hw0 : 0 < w := by omega
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw0
  have hA : 0 ≤ η * w / 2 := by positivity
  have hA2 : η * w / 2 * (2 / w) = η := by field_simp
  refine ⟨fun i hi => ?_, fun i j hij => ?_⟩
  · simp [pathθ, amp, hi]
  · have hj : j.val = i.val + 1 := hij
    have hdiff : pathθ (T := T) θ₀ w K (η * w / 2) u j - pathθ θ₀ w K (η * w / 2) u i =
        amp w K (η * w / 2) (i.val + 1) • sigN d K u ((i.val + 1 - 1) / w) -
          amp w K (η * w / 2) i.val • sigN d K u ((i.val - 1) / w) := by
      simp only [pathθ, hj]; abel
    rw [hdiff]
    set A := η * w / 2 with hAdef
    have nS := norm_sigN_le d K hd u
    rcases Nat.eq_zero_or_pos i.val with h0 | hpos
    · rw [h0, amp_zero, zero_smul, sub_zero, norm_smul, Real.norm_eq_abs]
      rcases amp_one w K A hw with h | h
      · calc _ ≤ A * (2 / w) * 1 := mul_le_mul h (by simpa using nS _) (norm_nonneg _) (by positivity)
          _ = η := by rw [mul_one, hA2]
      · exact absurd hA (not_le.2 h)
    · obtain ⟨c1, c2⟩ := amp_diff w K A hA hw i.val hpos
      by_cases hm : (i.val - 1) % w + 1 < w
      · have e : (i.val + 1 - 1) / w = (i.val - 1) / w := by
          rcases blk_succ w i.val hw0 hpos with ⟨_, h2, _⟩ | ⟨h1, _⟩
          · have : i.val + 1 - 1 = i.val := by omega
            rw [this, h2]
          · omega
        rw [e, ← sub_smul, norm_smul, Real.norm_eq_abs]
        calc _ ≤ A * (2 / w) * 1 := mul_le_mul (c1 hm) (nS _) (norm_nonneg _) (by positivity)
          _ = η := by rw [mul_one, hA2]
      · have hm' : (i.val - 1) % w + 1 = w := by
          have := Nat.mod_lt (i.val - 1) hw0
          omega
        obtain ⟨z, b⟩ := c2 hm'
        rw [z, zero_smul, sub_zero, norm_smul, Real.norm_eq_abs]
        calc _ ≤ A * (2 / w) * 1 := mul_le_mul b (nS _) (norm_nonneg _) (by positivity)
          _ = η := by rw [mul_one, hA2]

end TRS.Dev.TrackingFloor

end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement

noncomputable section

namespace TRS.Dev.TrackingFloor

/-- Flip the sign of coordinate `c` in block `q`. -/
def flip {d K : ℕ} (u : Fin K × Fin d → Bool) (q : Fin K) (c : Fin d) : Fin K × Fin d → Bool :=
  Function.update u (q, c) (!u (q, c))

lemma flip_flip {d K : ℕ} (u : Fin K × Fin d → Bool) (q : Fin K) (c : Fin d) :
    flip (flip u q c) q c = u := by
  unfold flip
  funext x
  by_cases h : x = (q, c)
  · subst h; simp
  · simp [Function.update_of_ne h]

lemma flip_ne {d K : ℕ} (u : Fin K × Fin d → Bool) (q : Fin K) (c : Fin d) :
    flip u q c (q, c) = !u (q, c) := by simp [flip]

lemma norm_sig_flip (d K : ℕ) (hd : 0 < d) (u : Fin K × Fin d → Bool) (q : Fin K) (c : Fin d) :
    ‖sig d K (flip u q c) q - sig d K u q‖ ^ 2 = 4 / d := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  rw [EuclideanSpace.norm_sq_eq, Finset.sum_eq_single c]
  · simp only [sig, PiLp.sub_apply, PiLp.toLp_apply, Real.norm_eq_abs, sq_abs, flip_ne]
    have : ∀ b : Bool, ((sgn (!b) / Real.sqrt d - sgn b / Real.sqrt d)) ^ 2 = 4 / d := by
      intro b
      have h2 : Real.sqrt d ^ 2 = d := Real.sq_sqrt hd'.le
      cases b <;> simp [sgn] <;> field_simp <;> nlinarith [h2]
    exact this _
  · intro c' _ hc'
    simp only [sig, PiLp.sub_apply, PiLp.toLp_apply, flip]
    have : Function.update u (q, c) (!u (q, c)) (q, c') = u (q, c') :=
      Function.update_of_ne (by simpa using hc') _ _
    simp [this]
  · simp

lemma sigN_flip_of_ne {d K : ℕ} (u : Fin K × Fin d → Bool) (q : Fin K) (c : Fin d) (k : ℕ)
    (hk : k ≠ q.val) : sigN d K (flip u q c) k = sigN d K u k := by
  unfold sigN
  split_ifs with h
  · have : (⟨k, h⟩ : Fin K) ≠ q := fun e => hk (by simpa using congrArg Fin.val e)
    unfold sig flip
    congr 1
    funext c'
    have : Function.update u (q, c) (!u (q, c)) (⟨k, h⟩, c') = u (⟨k, h⟩, c') :=
      Function.update_of_ne (fun e => this (by simpa using congrArg Prod.fst e)) _ _
    rw [this]
  · rfl

/-- The delta of two flipped paths. -/
lemma delta_sq {T d : ℕ} (θ₀ : Vector d) (hd : 0 < d) (w K : ℕ) (A : ℝ)
    (u : Fin K × Fin d → Bool) (q : Fin K) (c : Fin d) (r : Fin T) :
    ‖pathθ (T := T) θ₀ w K A (flip u q c) r - pathθ θ₀ w K A u r‖ ^ 2 =
      if (r.val - 1) / w = q.val then amp w K A r.val ^ 2 * (4 / d) else 0 := by
  unfold pathθ
  rw [add_sub_add_left_eq_sub, ← smul_sub]
  split_ifs with h
  · have : sigN d K (flip u q c) ((r.val - 1) / w) - sigN d K u ((r.val - 1) / w) =
        sig d K (flip u q c) q - sig d K u q := by
      rw [h]; simp [sigN, q.2]
    rw [this, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, norm_sig_flip d K hd]
  · rw [sigN_flip_of_ne u q c _ h]; simp

lemma delta_sq_le {T d : ℕ} (θ₀ : Vector d) (hd : 0 < d) (w K : ℕ) (hw : 0 < w) (A : ℝ)
    (hA : 0 ≤ A) (u : Fin K × Fin d → Bool) (q : Fin K) (c : Fin d) (r : Fin T) :
    ‖pathθ (T := T) θ₀ w K A (flip u q c) r - pathθ θ₀ w K A u r‖ ^ 2 ≤ 4 * A ^ 2 / d := by
  rw [delta_sq θ₀ hd w K A u q c r]
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  split_ifs
  · have := abs_amp_le w K A hA hw r.val
    have h2 : amp w K A r.val ^ 2 ≤ A ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
    calc _ ≤ A ^ 2 * (4 / d) := by gcongr
      _ = _ := by ring
  · positivity

lemma delta_sum_le {T d : ℕ} (θ₀ : Vector d) (hd : 0 < d) (w K : ℕ) (hw : 0 < w) (A : ℝ)
    (hA : 0 ≤ A) (u : Fin K × Fin d → Bool) (q : Fin K) (c : Fin d) :
    ∑ r : Fin T, ‖pathθ (T := T) θ₀ w K A (flip u q c) r - pathθ θ₀ w K A u r‖ ^ 2 ≤
      w * (4 * A ^ 2 / d) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  set S : Finset (Fin T) := Finset.univ.filter (fun r : Fin T => 1 ≤ r.val ∧ (r.val - 1) / w = q.val)
  have h1 : ∀ r : Fin T, ‖pathθ (T := T) θ₀ w K A (flip u q c) r - pathθ θ₀ w K A u r‖ ^ 2 ≤
      if r ∈ S then 4 * A ^ 2 / d else 0 := by
    intro r
    by_cases hr : r ∈ S
    · rw [if_pos hr]; exact delta_sq_le θ₀ hd w K hw A hA u q c r
    · rw [if_neg hr, delta_sq θ₀ hd w K A u q c r]
      split_ifs with h
      · have : r.val = 0 := by
          by_contra hne
          exact hr (by simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨by omega, h⟩)
        simp [this, amp_zero]
      · exact le_refl _
  have hcard : S.card ≤ w := by
    have : S.card ≤ (Finset.range w).card := by
      refine Finset.card_le_card_of_injOn (fun r : Fin T => (r.val - 1) % w) ?_ ?_
      · intro r _
        simp only [Finset.coe_range, Set.mem_Iio]
        exact Nat.mod_lt _ hw
      · intro r hr r' hr' h
        simp only [S, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hr hr'
        apply Fin.ext
        have e1 := Nat.div_add_mod (r.val - 1) w
        have e2 := Nat.div_add_mod (r'.val - 1) w
        simp only at h
        rw [hr.2] at e1
        rw [hr'.2] at e2
        omega
    simpa using this
  calc _ ≤ ∑ r : Fin T, (if r ∈ S then 4 * A ^ 2 / d else 0) := Finset.sum_le_sum fun r _ => h1 r
    _ = S.card * (4 * A ^ 2 / d) := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        simp [S]
    _ ≤ w * (4 * A ^ 2 / d) := by
        have : (S.card : ℝ) ≤ w := by exact_mod_cast hcard
        gcongr

/-! ## Numerics for the likelihood-ratio second moment -/

lemma inv_sqrt_le_exp (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 4) :
    1 / Real.sqrt (1 - 2 * x) ≤ Real.exp (2 * x) := by
  have hpos : 0 < 1 - 2 * x := by linarith
  have ht := Real.quadratic_le_exp_of_nonneg (x := 4 * x) (by linarith)
  have hexp : Real.exp (-(4 * x)) ≤ 1 - 2 * x := by
    rw [Real.exp_neg]
    have hp : 0 < Real.exp (4 * x) := Real.exp_pos _
    rw [inv_le_iff_one_le_mul₀ hp]
    nlinarith [mul_nonneg h0 h0, mul_nonneg (mul_nonneg h0 h0) h0, mul_nonneg h0 (sub_nonneg.2 h1)]
  have hs : Real.exp (-(2 * x)) ≤ Real.sqrt (1 - 2 * x) := by
    apply Real.le_sqrt_of_sq_le
    rw [← Real.exp_nat_mul]
    push_cast
    convert hexp using 2; ring
  rw [div_le_iff₀ (Real.sqrt_pos.2 hpos)]
  calc (1 : ℝ) = Real.exp (2 * x) * Real.exp (-(2 * x)) := by rw [← Real.exp_add]; simp
    _ ≤ _ := by gcongr

lemma exp_27_32 : Real.exp (27 / 32) ≤ 13 / 5 := by
  have h : Real.exp (27 / 128) ≤ 128 / 101 := by
    have := Real.exp_bound_div_one_sub_of_interval' (x := 27 / 128) (by norm_num) (by norm_num)
    refine this.le.trans (le_of_eq ?_)
    norm_num
  have : Real.exp (27 / 32) = Real.exp (27 / 128) ^ 4 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc Real.exp (27 / 128) ^ 4 ≤ (128 / 101 : ℝ) ^ 4 := by gcongr
    _ ≤ 13 / 5 := by norm_num

lemma prod_inv_sqrt_le {T : ℕ} (x : Fin T → ℝ) (h0 : ∀ i, 0 ≤ x i) (h1 : ∀ i, x i ≤ 1 / 4)
    (s : ℝ) (hs : ∑ i, x i ≤ s) :
    ∏ i, (1 / Real.sqrt (1 - 2 * x i)) ≤ Real.exp (2 * s) := by
  calc _ ≤ ∏ i, Real.exp (2 * x i) :=
        Finset.prod_le_prod (fun i _ => by
          have : 0 < 1 - 2 * x i := by linarith [h1 i]
          positivity) (fun i _ => inv_sqrt_le_exp _ (h0 i) (h1 i))
    _ = Real.exp (2 * ∑ i, x i) := by rw [← Real.exp_sum, Finset.mul_sum]
    _ ≤ _ := Real.exp_le_exp.2 (by linarith)

/-- Second moment of the flip likelihood ratio: all hypotheses packaged. -/
lemma chi_bound {T d : ℕ} (θ₀ : Vector d) (hd : 0 < d) (w K : ℕ) (hw : 0 < w) (η : ℝ) (hη : 0 ≤ η)
    (hs : η ^ 2 * (w : ℝ) ^ 3 ≤ 27 / 64 * d) (hx : η ^ 2 * (w : ℝ) ^ 2 ≤ d / 4)
    (u : Fin K × Fin d → Bool) (q : Fin K) (c : Fin d) :
    (∀ r : Fin T, 2 * ‖pathθ (T := T) θ₀ w K (η * w / 2) (flip u q c) r -
        pathθ θ₀ w K (η * w / 2) u r‖ ^ 2 < 1) ∧
    ∏ r : Fin T, (1 / Real.sqrt (1 - 2 * ‖pathθ (T := T) θ₀ w K (η * w / 2) (flip u q c) r -
        pathθ θ₀ w K (η * w / 2) u r‖ ^ 2)) ≤ 13 / 5 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hA : 0 ≤ η * w / 2 := by positivity
  have hind := delta_sq_le (T := T) θ₀ hd w K hw (η * w / 2) hA u q c
  have e4 : 4 * (η * w / 2) ^ 2 / d = η ^ 2 * w ^ 2 / d := by ring
  have hind' : ∀ r : Fin T, ‖pathθ (T := T) θ₀ w K (η * w / 2) (flip u q c) r -
        pathθ θ₀ w K (η * w / 2) u r‖ ^ 2 ≤ 1 / 4 := by
    intro r
    refine (hind r).trans ?_
    rw [e4, div_le_iff₀ hd']
    linarith
  refine ⟨fun r => by linarith [hind' r], ?_⟩
  have hsum := delta_sum_le (T := T) θ₀ hd w K hw (η * w / 2) hA u q c
  have e5 : (w : ℝ) * (4 * (η * w / 2) ^ 2 / d) = η ^ 2 * w ^ 3 / d := by ring
  rw [e5] at hsum
  have hsum' : η ^ 2 * (w : ℝ) ^ 3 / d ≤ 27 / 64 := by
    rw [div_le_iff₀ hd']; linarith
  refine (prod_inv_sqrt_le _ (fun r => by positivity) hind' (27 / 64) (hsum.trans hsum')).trans ?_
  have : Real.exp (2 * (27 / 64)) = Real.exp (27 / 32) := by norm_num
  rw [this]; exact exp_27_32

end TRS.Dev.TrackingFloor

end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement

noncomputable section

namespace TRS.Dev.TrackingFloor

lemma info_le {s : RandomSeed} {T d : ℕ} (n : ℕ) :
    information s T d n ≤ (inferInstance : MeasurableSpace (Transcript s T d)) := by
  have hF : Measurable (fun ω : Transcript s T d =>
      (ω.1, fun i : Fin T => if i.val < n then ω.2 i else (0, 0))) := by
    refine measurable_fst.prodMk (measurable_pi_lambda _ fun i => ?_)
    by_cases h : i.val < n
    · simp only [h, if_true]
      exact (measurable_pi_apply i).comp measurable_snd
    · simp [h]
  exact hF.comap_le

lemma measurable_deployed {s : RandomSeed} {T d B : ℕ} (θ₀ : Vector d) (π : ReleasePolicy s T d B)
    (hπ : IsCausal π) (i : Fin T) :
    Measurable (fun ω : Transcript s T d => deployed θ₀ π ω i) := by
  have hdate : ∀ j, MeasurableSet {ω : Transcript s T d | π.date j ω ≤ i.val} :=
    fun j => info_le i.val _ (hπ.2.2.1 j i.val)
  have hhead : ∀ j, Measurable (fun ω : Transcript s T d =>
      if π.date j ω ≤ i.val then π.head j ω else 0) :=
    fun j => (hπ.2.2.2 j i.val).mono (info_le i.val) le_rfl
  have key : ∀ (l : List (Fin B)) (w0 : Transcript s T d → Vector d), Measurable w0 →
      Measurable fun ω => l.foldl (fun w j => if π.date j ω ≤ i.val then π.head j ω else w) (w0 ω) := by
    intro l
    induction l with
    | nil => intro w0 hw0; simpa using hw0
    | cons j l ih =>
      intro w0 hw0
      simp only [List.foldl_cons]
      apply ih
      have : Measurable fun ω : Transcript s T d =>
          if π.date j ω ≤ i.val then (if π.date j ω ≤ i.val then π.head j ω else 0) else w0 ω :=
        Measurable.ite (hdate j) (hhead j) hw0
      convert this using 2 with ω
      by_cases h : π.date j ω ≤ i.val <;> simp [h]
  unfold deployed
  exact key _ (fun _ => θ₀) measurable_const

end TRS.Dev.TrackingFloor

end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement

noncomputable section

namespace TRS.Dev.TrackingFloor

def coordErr {s : RandomSeed} {T d B : ℕ} (θ₀ : Vector d) (π : ReleasePolicy s T d B)
    (θ : Fin T → Vector d) (r : Fin T) (c : Fin d) : ℝ≥0∞ :=
  ∫⁻ ω : s.space × GaussianRows T d,
    ENNReal.ofReal ((1 / 2 : ℝ) *
      (deployed θ₀ π (ω.1, observations θ ω.2) r c - θ r c) ^ 2)
    ∂(s.law.prod (gaussianRows T d))

lemma path_coord {T d : ℕ} (θ₀ : Vector d) (w K : ℕ) (A : ℝ) (u : Fin K × Fin d → Bool)
    (q : Fin K) (c : Fin d) (r : Fin T) (hq : (r.val - 1) / w = q.val) :
    pathθ (T := T) θ₀ w K A u r c = θ₀ c + amp w K A r.val * (sgn (u (q, c)) / Real.sqrt d) := by
  simp only [pathθ, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hq, sigN, q.2, dif_pos, sig,
    PiLp.toLp_apply]

lemma pair {s : RandomSeed} {T d B : ℕ} (θ₀ : Vector d) (hd : 0 < d)
    (π : ReleasePolicy s T d B) (hπ : IsCausal π) (w K : ℕ) (hw : 2 ≤ w) (η : ℝ) (hη : 0 ≤ η)
    (hs : η ^ 2 * (w : ℝ) ^ 3 ≤ 27 / 64 * d) (hx : η ^ 2 * (w : ℝ) ^ 2 ≤ d / 4)
    (u : Fin K × Fin d → Bool) (q : Fin K) (c : Fin d) (hu : u (q, c) = true)
    (r : Fin T) (hrq : (r.val - 1) / w = q.val) :
    ENNReal.ofReal ((amp w K (η * w / 2) r.val / Real.sqrt d) ^ 2 / 2 * (7 / 20)) ≤
      coordErr θ₀ π (pathθ θ₀ w K (η * w / 2) u) r c +
      coordErr θ₀ π (pathθ θ₀ w K (η * w / 2) (flip u q c)) r c := by
  have hw0 : 0 < w := by omega
  have hA : 0 ≤ η * w / 2 := by positivity
  set A := η * w / 2 with hAdef
  set θ := pathθ (T := T) θ₀ w K A u with hθ
  set θ' := pathθ (T := T) θ₀ w K A (flip u q c) with hθ'
  set a : ℝ := amp w K A r.val / Real.sqrt d with ha
  have ha0 : 0 ≤ a := div_nonneg (amp_nonneg w K A hA hw0 _) (Real.sqrt_nonneg _)
  have hθc : θ r c = θ₀ c + a := by
    rw [hθ, path_coord θ₀ w K A u q c r hrq, hu]; simp [sgn, ha, div_eq_mul_inv]
  have hθ'c : θ' r c = θ₀ c - a := by
    rw [hθ', path_coord θ₀ w K A _ q c r hrq, flip_ne, hu]; simp [sgn, ha, div_eq_mul_inv]; ring
  set g : s.space × Data T d → ℝ := fun ω => deployed θ₀ π ω r c - θ₀ c with hg
  have hgm : Measurable g := by
    have h1 := measurable_deployed θ₀ π hπ r
    have : Measurable fun ω : Transcript s T d => (deployed θ₀ π ω r) c :=
      ((PiLp.continuous_apply 2 _ c).measurable.comp h1)
    exact this.sub_const _
  set μ := s.law.prod (gaussianRows T d) with hμ
  have : IsProbabilityMeasure (gaussianRows T d) := by unfold gaussianRows; infer_instance
  have hμp : IsProbabilityMeasure μ := by rw [hμ]; infer_instance
  obtain ⟨hlt, hprod⟩ := chi_bound (T := T) θ₀ hd w K hw0 η hη hs hx u q c
  have h2 := two_point θ θ' g hgm hlt (13 / 5) hprod
  -- lower bounds for the two coordinate errors
  have hE := measurableSet_Ev g hgm θ
  have hE' := measurableSet_Ev g hgm θ'
  have lb1 : ENNReal.ofReal (a ^ 2 / 2) * μ (Ev g θ) ≤ coordErr θ₀ π θ r c := by
    unfold coordErr
    rw [← lintegral_indicator_one hE, ← lintegral_const_mul _ (measurable_one.indicator hE)]
    refine lintegral_mono fun ω => ?_
    by_cases h : ω ∈ Ev g θ
    · rw [Set.indicator_of_mem h, Pi.one_apply, mul_one]
      apply ENNReal.ofReal_le_ofReal
      have h' : g (ω.1, observations θ ω.2) ≤ 0 := h
      simp only [hg] at h'
      rw [hθc]
      nlinarith
    · rw [Set.indicator_of_notMem h]; simp
  have lb2 : ENNReal.ofReal (a ^ 2 / 2) * μ (Ev g θ')ᶜ ≤ coordErr θ₀ π θ' r c := by
    unfold coordErr
    rw [← lintegral_indicator_one hE'.compl, ← lintegral_const_mul _ (measurable_one.indicator hE'.compl)]
    refine lintegral_mono fun ω => ?_
    by_cases h : ω ∈ (Ev g θ')ᶜ
    · rw [Set.indicator_of_mem h, Pi.one_apply, mul_one]
      apply ENNReal.ofReal_le_ofReal
      have h' : 0 < g (ω.1, observations θ' ω.2) := by
        simpa [Ev] using h
      simp only [hg] at h'
      rw [hθ'c]
      nlinarith
    · rw [Set.indicator_of_notMem h]; simp
  -- probabilities
  have hsum : ENNReal.ofReal (7 / 20) ≤ μ (Ev g θ) + μ (Ev g θ')ᶜ := by
    rw [ENNReal.ofReal_le_iff_le_toReal (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩),
      ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    have : (μ (Ev g θ')ᶜ).toReal = 1 - (μ (Ev g θ')).toReal := by
      rw [prob_compl_eq_one_sub hE', ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top]
      simp
    rw [this]
    linarith
  calc ENNReal.ofReal ((amp w K (η * w / 2) r.val / Real.sqrt d) ^ 2 / 2 * (7 / 20))
      = ENNReal.ofReal (a ^ 2 / 2) * ENNReal.ofReal (7 / 20) := by
        rw [ENNReal.ofReal_mul (by positivity)]
    _ ≤ ENNReal.ofReal (a ^ 2 / 2) * (μ (Ev g θ) + μ (Ev g θ')ᶜ) := by gcongr
    _ = ENNReal.ofReal (a ^ 2 / 2) * μ (Ev g θ) + ENNReal.ofReal (a ^ 2 / 2) * μ (Ev g θ')ᶜ := by
        rw [mul_add]
    _ ≤ _ := add_le_add lb1 lb2

end TRS.Dev.TrackingFloor

end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement

noncomputable section

namespace TRS.Dev.TrackingFloor

lemma measurable_coordTerm {s : RandomSeed} {T d B : ℕ} (θ₀ : Vector d) (π : ReleasePolicy s T d B)
    (hπ : IsCausal π) (θ : Fin T → Vector d) (r : Fin T) (c : Fin d) :
    Measurable fun ω : s.space × GaussianRows T d =>
      ENNReal.ofReal ((1 / 2 : ℝ) * (deployed θ₀ π (ω.1, observations θ ω.2) r c - θ r c) ^ 2) := by
  have h1 := (measurable_deployed θ₀ π hπ r).comp
    (measurable_fst.prodMk ((measurable_observations θ).comp measurable_snd) :
      Measurable fun ω : s.space × GaussianRows T d => (ω.1, observations θ ω.2))
  have h2 : Measurable fun ω : s.space × GaussianRows T d =>
      (deployed θ₀ π (ω.1, observations θ ω.2) r) c :=
    (PiLp.continuous_apply 2 _ c).measurable.comp h1
  exact (((h2.sub_const _).pow_const 2).const_mul _).ennreal_ofReal

lemma risk_ge_sum {s : RandomSeed} {T d B : ℕ} (θ₀ : Vector d) (π : ReleasePolicy s T d B)
    (hπ : IsCausal π) (θ : Fin T → Vector d) {ι : Type} (R : ι → Fin T)
    (hR : Function.Injective R) (Pairs : Finset ι) :
    ∑ x ∈ Pairs, ∑ c : Fin d, coordErr θ₀ π θ (R x) c ≤ policyRisk θ₀ π θ := by
  unfold coordErr policyRisk
  have hm : ∀ x ∈ Pairs, Measurable fun ω : s.space × GaussianRows T d =>
      ∑ c : Fin d, ENNReal.ofReal ((1 / 2 : ℝ) *
        (deployed θ₀ π (ω.1, observations θ ω.2) (R x) c - θ (R x) c) ^ 2) :=
    fun x _ => Finset.measurable_sum _ fun c _ => measurable_coordTerm θ₀ π hπ θ (R x) c
  have e0 : ∀ x ∈ Pairs, ∑ c : Fin d, ∫⁻ ω : s.space × GaussianRows T d,
      ENNReal.ofReal ((1 / 2 : ℝ) * (deployed θ₀ π (ω.1, observations θ ω.2) (R x) c - θ (R x) c) ^ 2)
        ∂(s.law.prod (gaussianRows T d)) = ∫⁻ ω : s.space × GaussianRows T d,
      ∑ c : Fin d, ENNReal.ofReal ((1 / 2 : ℝ) *
        (deployed θ₀ π (ω.1, observations θ ω.2) (R x) c - θ (R x) c) ^ 2)
        ∂(s.law.prod (gaussianRows T d)) := fun x _ =>
    (lintegral_finsetSum _ fun c _ => measurable_coordTerm θ₀ π hπ θ (R x) c).symm
  rw [Finset.sum_congr rfl e0]
  rw [← lintegral_finsetSum _ hm]
  refine lintegral_mono fun ω => ?_
  set v : Fin T → Vector d := fun i => deployed θ₀ π (ω.1, observations θ ω.2) i - θ i with hv
  have e1 : ∀ x, ∑ c : Fin d, ENNReal.ofReal ((1 / 2 : ℝ) *
        (deployed θ₀ π (ω.1, observations θ ω.2) (R x) c - θ (R x) c) ^ 2) =
      ENNReal.ofReal ((1 / 2 : ℝ) * ‖v (R x)‖ ^ 2) := by
    intro x
    rw [← ENNReal.ofReal_sum_of_nonneg (fun c _ => by positivity), ← Finset.mul_sum,
      EuclideanSpace.real_norm_sq_eq]
    rfl
  simp_rw [e1]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => by positivity), ← Finset.mul_sum]
  apply ENNReal.ofReal_le_ofReal
  gcongr
  rw [← Finset.sum_image (f := fun i => ‖v i‖ ^ 2) (fun x _ y _ h => hR h)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => by positivity)

/-- Averaging over the flip of one coordinate. -/
lemma avg_flip {s : RandomSeed} {T d B : ℕ} (θ₀ : Vector d) (hd : 0 < d)
    (π : ReleasePolicy s T d B) (hπ : IsCausal π) (w K : ℕ) (hw : 2 ≤ w) (η : ℝ) (hη : 0 ≤ η)
    (hs : η ^ 2 * (w : ℝ) ^ 3 ≤ 27 / 64 * d) (hx : η ^ 2 * (w : ℝ) ^ 2 ≤ d / 4)
    (q : Fin K) (c : Fin d) (r : Fin T) (hrq : (r.val - 1) / w = q.val) :
    (Fintype.card (Fin K × Fin d → Bool) : ℝ≥0∞) *
        ENNReal.ofReal ((amp w K (η * w / 2) r.val / Real.sqrt d) ^ 2 / 2 * (7 / 20)) ≤
      2 * ∑ u : Fin K × Fin d → Bool,
        coordErr θ₀ π (pathθ θ₀ w K (η * w / 2) u) r c := by
  set f : (Fin K × Fin d → Bool) → ℝ≥0∞ := fun u => coordErr θ₀ π (pathθ θ₀ w K (η * w / 2) u) r c
    with hf
  set LB := ENNReal.ofReal ((amp w K (η * w / 2) r.val / Real.sqrt d) ^ 2 / 2 * (7 / 20))
  have hpair : ∀ u : Fin K × Fin d → Bool, LB ≤ f u + f (flip u q c) := by
    intro u
    by_cases hu : u (q, c) = true
    · exact pair θ₀ hd π hπ w K hw η hη hs hx u q c hu r hrq
    · have hu' : flip u q c (q, c) = true := by
        rw [flip_ne]; simpa using hu
      have := pair θ₀ hd π hπ w K hw η hη hs hx (flip u q c) q c hu' r hrq
      rw [flip_flip] at this
      rwa [add_comm] at this
  have hbij : ∑ u, f (flip u q c) = ∑ u, f u := by
    refine Fintype.sum_equiv ⟨fun u => flip u q c, fun u => flip u q c, fun u => flip_flip u q c,
      fun u => flip_flip u q c⟩ _ _ fun u => rfl
  calc (Fintype.card (Fin K × Fin d → Bool) : ℝ≥0∞) * LB
      = ∑ _u : Fin K × Fin d → Bool, LB := by simp
    _ ≤ ∑ u, (f u + f (flip u q c)) := Finset.sum_le_sum fun u _ => hpair u
    _ = ∑ u, f u + ∑ u, f (flip u q c) := Finset.sum_add_distrib
    _ = 2 * ∑ u, f u := by rw [hbij, two_mul]

end TRS.Dev.TrackingFloor

end
end

section
set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement

noncomputable section

namespace TRS.Dev.TrackingFloor

def goodSet (w : ℕ) : Finset (Fin w) :=
  Finset.univ.filter (fun m : Fin w => (w + 3) / 4 ≤ m.val + 1 ∧ m.val + 1 ≤ 3 * w / 4)

lemma four_card_goodSet (w : ℕ) (hw2 : 2 ≤ w) : w ≤ 4 * (goodSet w).card := by
  have hw : 0 < w := by omega
  have h1 : (Finset.Icc ((w + 3) / 4) (3 * w / 4)).card ≤ (goodSet w).card := by
    refine Finset.card_le_card_of_injOn
      (fun p : ℕ => if h : p - 1 < w then (⟨p - 1, h⟩ : Fin w) else ⟨0, hw⟩) ?_ ?_
    · intro p hp
      simp only [Finset.coe_Icc, Set.mem_Icc] at hp
      have h : p - 1 < w := by omega
      simp only [goodSet, dif_pos h, Finset.coe_filter, Finset.mem_univ, true_and,
        Set.mem_setOf_eq]
      omega
    · intro p hp p' hp' hpp
      simp only [Finset.coe_Icc, Set.mem_Icc] at hp hp'
      have h : p - 1 < w := by omega
      have h' : p' - 1 < w := by omega
      simp only [dif_pos h, dif_pos h', Fin.mk.injEq] at hpp
      omega
  rw [Nat.card_Icc] at h1
  omega

def rr {T : ℕ} (w K : ℕ) (hK : K * w + 1 ≤ T) (x : Fin K × Fin w) : Fin T :=
  ⟨w * x.1.val + x.2.val + 1, by
    have h1 : x.1.val + 1 ≤ K := x.1.2
    have h2 : w * (x.1.val + 1) ≤ w * K := Nat.mul_le_mul_left _ h1
    have h3 := x.2.2
    nlinarith⟩

lemma rr_div {T : ℕ} (w K : ℕ) (hK : K * w + 1 ≤ T) (x : Fin K × Fin w) :
    ((rr w K hK x).val - 1) / w = x.1.val ∧ ((rr w K hK x).val - 1) % w = x.2.val := by
  have := blk_pos w x.1.val (x.2.val + 1) (by omega) (by have := x.2.2; omega)
  simp only [rr]
  have e : w * x.1.val + x.2.val + 1 - 1 = w * x.1.val + (x.2.val + 1) - 1 := by omega
  rw [e]
  simpa using this

lemma rr_inj {T : ℕ} (w K : ℕ) (hK : K * w + 1 ≤ T) : Function.Injective (rr (T := T) w K hK) := by
  intro x y h
  have h1 := rr_div w K hK x
  have h2 := rr_div w K hK y
  rw [h] at h1
  have a1 : x.1.val = y.1.val := h1.1.symm.trans h2.1
  have a2 : x.2.val = y.2.val := h1.2.symm.trans h2.2
  exact Prod.ext (Fin.ext a1) (Fin.ext a2)

lemma amp_rr {T : ℕ} (w K : ℕ) (hK : K * w + 1 ≤ T) (A : ℝ) (x : Fin K × Fin w) :
    amp w K A (rr w K hK x).val = A * hh w (x.2.val + 1) := by
  obtain ⟨h1, h2⟩ := rr_div w K hK x
  unfold amp
  rw [h1, h2, if_pos ⟨by simp [rr], x.1.2⟩]

theorem main_lb {s : RandomSeed} {T d B : ℕ} (θ₀ : Vector d) (hd : 0 < d)
    (π : ReleasePolicy s T d B) (hπ : IsCausal π) (w K : ℕ) (hw : 2 ≤ w) (hK : K * w + 1 ≤ T)
    (η : ℝ) (hη : 0 ≤ η)
    (hs : η ^ 2 * (w : ℝ) ^ 3 ≤ 27 / 64 * d) (hx : η ^ 2 * (w : ℝ) ^ 2 ≤ d / 4) :
    ENNReal.ofReal (7 * ((K : ℝ) * (goodSet w).card) * (η * w / 2) ^ 2 / 320) ≤
      driftWorstRisk θ₀ 0 η π := by
  have hw0 : 0 < w := by omega
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  set A := η * w / 2 with hAdef
  have hA : 0 ≤ A := by positivity
  set W := driftWorstRisk θ₀ 0 η π with hW
  set Pairs : Finset (Fin K × Fin w) := Finset.univ ×ˢ goodSet w with hPairs
  set N : ℝ≥0∞ := (Fintype.card (Fin K × Fin d → Bool) : ℝ≥0∞) with hN
  have hN0 : N ≠ 0 := by
    rw [hN]; simp
  have hNt : N ≠ ⊤ := by rw [hN]; exact ENNReal.natCast_ne_top _
  have hrisk : ∀ u : Fin K × Fin d → Bool, policyRisk θ₀ π (pathθ (T := T) θ₀ w K A u) ≤ W := by
    intro u
    exact le_iSup (fun θ : ↥(driftClass (T := T) θ₀ 0 η) => policyRisk θ₀ π θ.val)
      ⟨_, pathθ_mem θ₀ hd w K hw η hη u⟩
  -- step 1: sum of coordinate errors bounded by N * W
  have step1 : ∑ u : Fin K × Fin d → Bool, ∑ x ∈ Pairs, ∑ c : Fin d,
      coordErr θ₀ π (pathθ (T := T) θ₀ w K A u) (rr w K hK x) c ≤ N * W := by
    calc _ ≤ ∑ u : Fin K × Fin d → Bool, W :=
          Finset.sum_le_sum fun u _ =>
            (risk_ge_sum θ₀ π hπ _ (rr w K hK) (rr_inj w K hK) Pairs).trans (hrisk u)
      _ = N * W := by simp [hN]
  -- step 2: lower bound via averaging
  set LB : Fin K × Fin w → Fin d → ℝ≥0∞ := fun x c =>
    ENNReal.ofReal ((amp w K A (rr w K hK x).val / Real.sqrt d) ^ 2 / 2 * (7 / 20)) with hLB
  have step2 : N * ∑ x ∈ Pairs, ∑ c : Fin d, LB x c ≤
      2 * ∑ u : Fin K × Fin d → Bool, ∑ x ∈ Pairs, ∑ c : Fin d,
        coordErr θ₀ π (pathθ (T := T) θ₀ w K A u) (rr w K hK x) c := by
    have hxc : ∀ x ∈ Pairs, ∀ c : Fin d, N * LB x c ≤
        2 * ∑ u : Fin K × Fin d → Bool,
          coordErr θ₀ π (pathθ (T := T) θ₀ w K A u) (rr w K hK x) c := by
      intro x _ c
      obtain ⟨h1, _⟩ := rr_div w K hK x
      exact avg_flip θ₀ hd π hπ w K hw η hη hs hx x.1 c (rr w K hK x) h1
    calc N * ∑ x ∈ Pairs, ∑ c : Fin d, LB x c = ∑ x ∈ Pairs, ∑ c : Fin d, N * LB x c := by
          simp_rw [Finset.mul_sum]
      _ ≤ ∑ x ∈ Pairs, ∑ c : Fin d, 2 * ∑ u : Fin K × Fin d → Bool,
          coordErr θ₀ π (pathθ (T := T) θ₀ w K A u) (rr w K hK x) c :=
        Finset.sum_le_sum fun x hx' => Finset.sum_le_sum fun c _ => hxc x hx' c
      _ = 2 * ∑ x ∈ Pairs, ∑ c : Fin d, ∑ u : Fin K × Fin d → Bool,
          coordErr θ₀ π (pathθ (T := T) θ₀ w K A u) (rr w K hK x) c := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
      _ = 2 * ∑ u : Fin K × Fin d → Bool, ∑ x ∈ Pairs, ∑ c : Fin d,
          coordErr θ₀ π (pathθ (T := T) θ₀ w K A u) (rr w K hK x) c := by
          congr 1
          have h1 : ∀ x ∈ Pairs, ∑ c : Fin d, ∑ u : Fin K × Fin d → Bool,
              coordErr θ₀ π (pathθ (T := T) θ₀ w K A u) (rr w K hK x) c =
              ∑ u : Fin K × Fin d → Bool, ∑ c : Fin d,
              coordErr θ₀ π (pathθ (T := T) θ₀ w K A u) (rr w K hK x) c :=
            fun x _ => Finset.sum_comm
          rw [Finset.sum_congr rfl h1]
          exact Finset.sum_comm
  -- step 3: cancel N
  have step3 : ∑ x ∈ Pairs, ∑ c : Fin d, LB x c ≤ 2 * W := by
    have : N * ∑ x ∈ Pairs, ∑ c : Fin d, LB x c ≤ N * (2 * W) := by
      calc _ ≤ _ := step2
        _ = 2 * ∑ u : Fin K × Fin d → Bool, ∑ x ∈ Pairs, ∑ c : Fin d,
            coordErr θ₀ π (pathθ (T := T) θ₀ w K A u) (rr w K hK x) c := rfl
        _ ≤ 2 * (N * W) := by gcongr
        _ = N * (2 * W) := by ring
    exact (ENNReal.mul_le_mul_iff_right hN0 hNt).1 this
  -- step 4: each LB is at least a constant
  have hLB' : ∀ x ∈ Pairs, ∀ c : Fin d, ENNReal.ofReal (7 * A ^ 2 / (160 * d)) ≤ LB x c := by
    intro x hx'
    intro c
    simp only [hPairs, Finset.mem_product, Finset.mem_univ, true_and, goodSet,
      Finset.mem_filter] at hx'
    have hh1 := hh_half w (x.2.val + 1) hw0 hx'.1 hx'.2
    simp only [hLB]
    apply ENNReal.ofReal_le_ofReal
    have e : (A * hh w (x.2.val + 1) / Real.sqrt d) ^ 2 = A ^ 2 * hh w (x.2.val + 1) ^ 2 / d := by
      rw [div_pow, mul_pow, Real.sq_sqrt hd'.le]
    rw [amp_rr w K hK A x, e]
    have : (1 / 2 : ℝ) ^ 2 ≤ hh w (x.2.val + 1) ^ 2 := pow_le_pow_left₀ (by norm_num) hh1 2
    have hA2 : 0 ≤ A ^ 2 := by positivity
    rw [show 7 * A ^ 2 / (160 * (d : ℝ)) = A ^ 2 * (1 / 4) / d / 2 * (7 / 20) by field_simp; ring]
    gcongr
    nlinarith
  have step4 : ENNReal.ofReal (7 * A ^ 2 / (160 * d)) * (Pairs.card * d : ℕ) ≤
      ∑ x ∈ Pairs, ∑ c : Fin d, LB x c := by
    calc _ = ∑ x ∈ Pairs, ∑ c : Fin d, ENNReal.ofReal (7 * A ^ 2 / (160 * d)) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ _ := Finset.sum_le_sum fun x hx' => Finset.sum_le_sum fun c _ => hLB' x hx' c
  -- step 5: conclude
  have hcard : (Pairs.card * d : ℕ) = K * (goodSet w).card * d := by
    simp [hPairs, Finset.card_product]
  rw [hcard] at step4
  have hfin : ENNReal.ofReal (7 * A ^ 2 / (160 * d)) * ((K * (goodSet w).card * d : ℕ) : ℝ≥0∞)
      = ENNReal.ofReal (7 * ((K : ℝ) * (goodSet w).card) * A ^ 2 / 160) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    push_cast
    field_simp
  rw [hfin] at step4
  have h2 : ENNReal.ofReal (7 * ((K : ℝ) * (goodSet w).card) * A ^ 2 / 320) * 2 ≤ 2 * W := by
    have : ENNReal.ofReal (7 * ((K : ℝ) * (goodSet w).card) * A ^ 2 / 160) =
        ENNReal.ofReal (7 * ((K : ℝ) * (goodSet w).card) * A ^ 2 / 320) * 2 := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by positivity)]
      congr 1; ring
    rw [← this]
    exact step4.trans step3
  rw [mul_comm] at h2
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).1 h2

end TRS.Dev.TrackingFloor

end
end

section
/-!
# PLAN (q382, Lemma 5.2 tracking floor)

Constants.  `y = (d/η²)^{1/3}`, `w = min(T-1, ⌊3y/4⌋)`, `K = ⌊(T-1)/w⌋`, `A = ηw/2`.
Prior: `u ∈ {±1}^{K×d}` uniform; round `r` (0-indexed), `r ≥ 1`, block `q = (r-1)/w < K`,
`pos = (r-1)%w + 1 ∈ [1,w]`, `θ_r = θ₀ + A h(pos) u(q)/√d` with the tent `h(i) = 1-|2i-w|/w`
(`θ_r = θ₀` for `r = 0` or `r > Kw`).  Increments `≤ 2A/w = η` (`pathθ_mem`).
(1) Hypotheses used: `η² y³ = d`, `y ≥ 4` (from `dη ≤ 1/8`), so `η²w³ ≤ 27d/64`, `η²w² ≤ d/4`.
(2) Two-point bound (`two_point`): flipping one coordinate `(q,c)` of `u` shears the labels of
    block `q` by `δ_r = ±2A h(pos)/√d e_c`; likelihood ratio `D = ∏ rowD(δ_r)`,
    `∫D² = ∏ (1-2‖δ_r‖²)^{-1/2} ≤ exp(2 Σ‖δ_r‖²) ≤ exp(2 η²w³/d) ≤ exp(27/32) ≤ 13/5 =: χ`
    (`chi_bound`).  With `E = {g ≤ 0}` and Cauchy-Schwarz `P'(E) ≤ sqrt(χ P(E)) ≤ P(E) + χ/4`.
    Hence `P(E) + P'(Eᶜ) ≥ 1 - χ/4 = 7/20`: a sign test (any measurable function of seed and all
    rows, in particular the deployed coordinate) errs with total prob. `≥ 7/20` over the pair.
(3) Pair (`pair`): the squared error in coordinate `c` at a round of block `q` is `≥ a²` when the
    sign is missed, `a = A h/√d`; so `coordErr(u)+coordErr(flip u) ≥ a²/2 · 7/20`.
(4) Average over `u` (`avg_flip`, `main_lb`): `sup_θ risk ≥ avg_u risk ≥ ½ Σ_{x,c} LB`, over good
    positions `h ≥ 1/2` (`goodSet`, `4|goodSet| ≥ w`), giving `7 K|G| A²/320`.
(5) Numerics: `8K|G| ≥ 2Kw ≥ T-1 ≥ 7T/8`, `φ ≤ 16A² = 4η²w²` (`2w ≥ min(T,y)`),
    so `2^{-13}Tφ ≤ T A²/512 ≤ 7 K|G| A²/320`.
Causality is used only for measurability of `deployed` (not for the information bound).
-/

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open TightReleaseSchedules.Stationary TightReleaseSchedules.Stationary.Supplement

noncomputable section

namespace TRS.Dev.TrackingFloor

lemma rate_eq (d : ℕ) (η y : ℝ) (hη : 0 < η) (hy : 0 < y) (hyd : η ^ 2 * y ^ 3 = d) :
    ((d : ℝ) * η) ^ (2 / 3 : ℝ) = η ^ 2 * y ^ 2 := by
  have h1 : (d : ℝ) * η = (η * y) ^ 3 := by rw [← hyd]; ring
  rw [h1, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num
  ring

lemma arith_aux (T X S φ : ℝ) (hT : 0 ≤ T) (hX : 7 * T / 64 ≤ X) (hS : 0 ≤ S) (hφ : T * φ ≤ T * (16 * S)) :
    1 / 8192 * T * φ ≤ 7 * X * S / 320 := by
  nlinarith [mul_le_mul_of_nonneg_right hX hS, mul_nonneg hT hS]

theorem final_numeric (T d : ℕ) (hT : 8 ≤ T) (hd : 0 < d) (η : ℝ) (hpos : 0 < η)
    (hdη : (d : ℝ) * η ≤ 1 / 8) :
    ∃ w K : ℕ, 2 ≤ w ∧ K * w + 1 ≤ T ∧
      η ^ 2 * (w : ℝ) ^ 3 ≤ 27 / 64 * d ∧ η ^ 2 * (w : ℝ) ^ 2 ≤ d / 4 ∧
      ∀ G : ℕ, w ≤ 4 * G →
      (2 : ℝ) ^ (-13 : ℤ) * T * trackingRate T d η ≤ 7 * ((K : ℝ) * G) * (η * w / 2) ^ 2 / 320 := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  set y : ℝ := ((d : ℝ) / η ^ 2) ^ (1 / 3 : ℝ) with hydef
  have hy0 : 0 < y := Real.rpow_pos_of_pos (by positivity) _
  have hy3 : y ^ 3 = d / η ^ 2 := by
    rw [hydef, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    norm_num
  have hyd : η ^ 2 * y ^ 3 = d := by rw [hy3]; field_simp
  have hη8 : η ≤ 1 / 8 := by nlinarith
  have hy4 : 4 ≤ y := by
    by_contra hcon
    push Not at hcon
    have : y ^ 3 < 4 ^ 3 := pow_lt_pow_left₀ hcon hy0.le (by norm_num)
    nlinarith [mul_pos hpos hpos]
  set w : ℕ := min (T - 1) ⌊3 * y / 4⌋₊ with hwdef
  have hfl : 3 ≤ ⌊3 * y / 4⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hw2 : 2 ≤ w := by rw [hwdef]; omega
  have hw0 : 0 < w := by omega
  have hwT : w ≤ T - 1 := min_le_left _ _
  have hwy : (w : ℝ) ≤ 3 * y / 4 :=
    (Nat.cast_le.2 (min_le_right _ _)).trans (Nat.floor_le (by positivity))
  have hw' : (0 : ℝ) < w := by exact_mod_cast hw0
  set K : ℕ := (T - 1) / w with hKdef
  have hKw : K * w ≤ T - 1 := Nat.div_mul_le_self _ _
  have hK1 : 1 ≤ K := Nat.div_pos hwT hw0
  have hTK : T - 1 < (K + 1) * w := by
    have := Nat.div_add_mod (T - 1) w
    have := Nat.mod_lt (T - 1) hw0
    rw [hKdef]; nlinarith
  refine ⟨w, K, hw2, by omega, ?_, ?_, ?_⟩
  · have : (w : ℝ) ^ 3 ≤ (3 * y / 4) ^ 3 := pow_le_pow_left₀ hw'.le hwy 3
    nlinarith [sq_nonneg η]
  · have h1 : (w : ℝ) ^ 2 ≤ (3 * y / 4) ^ 2 := pow_le_pow_left₀ hw'.le hwy 2
    have h2 : η ^ 2 * y ^ 2 * 4 ≤ d := by nlinarith [mul_nonneg (sq_nonneg η) (sq_nonneg y)]
    nlinarith [sq_nonneg η]
  · intro G hG
    -- φ ≤ 4 η² w²
    have hφ : trackingRate T d η ≤ 4 * η ^ 2 * (w : ℝ) ^ 2 := by
      unfold trackingRate
      rcases le_total (T - 1) ⌊3 * y / 4⌋₊ with h | h
      · have hwe : w = T - 1 := by rw [hwdef]; exact min_eq_left h
        refine (min_le_right _ _).trans ?_
        have : (w : ℝ) = (T : ℝ) - 1 := by
          rw [hwe, Nat.cast_sub (by omega)]; simp
        have hT8 : (8 : ℝ) ≤ T := by exact_mod_cast hT
        rw [this]
        have h5 : (T : ℝ) ^ 2 ≤ 4 * ((T : ℝ) - 1) ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_left h5 (sq_nonneg η)]
      · have hwe : w = ⌊3 * y / 4⌋₊ := by rw [hwdef]; exact min_eq_right h
        refine (min_le_left _ _).trans ?_
        rw [rate_eq d η y hpos hy0 hyd]
        have h3 := Nat.lt_floor_add_one (3 * y / 4)
        have : (w : ℝ) = ⌊3 * y / 4⌋₊ := by rw [hwe]
        have h4 : y ≤ 2 * w := by linarith
        have : y ^ 2 ≤ 4 * (w : ℝ) ^ 2 := by nlinarith
        nlinarith [sq_nonneg η]
    have hKw' : (K : ℝ) * w ≤ (T : ℝ) - 1 := by
      have : ((K * w : ℕ) : ℝ) ≤ ((T - 1 : ℕ) : ℝ) := by exact_mod_cast hKw
      rw [Nat.cast_sub (by omega)] at this
      push_cast at this; linarith
    have hTK' : (T : ℝ) - 1 ≤ 2 * K * w := by
      have h1 : T - 1 < (K + 1) * w := hTK
      have h2 : (K + 1) * w ≤ 2 * K * w := by nlinarith
      have : ((T - 1 : ℕ) : ℝ) ≤ ((2 * K * w : ℕ) : ℝ) := by exact_mod_cast (h1.trans_le h2).le
      rw [Nat.cast_sub (by omega)] at this
      push_cast at this; linarith
    have hG' : (w : ℝ) ≤ 4 * G := by exact_mod_cast hG
    have hT8 : (8 : ℝ) ≤ T := by exact_mod_cast hT
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    have hX : 7 * (T : ℝ) / 64 ≤ (K : ℝ) * G := by nlinarith
    have hA2 : 0 ≤ (η * w / 2) ^ 2 := sq_nonneg _
    have e13 : (2 : ℝ) ^ (-13 : ℤ) = 1 / 8192 := by norm_num
    rw [e13]
    have hTφ : (T : ℝ) * trackingRate T d η ≤ T * (16 * (η * w / 2) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc _ ≤ _ := hφ
        _ = 16 * (η * w / 2) ^ 2 := by ring
    exact arith_aux _ _ _ _ (by positivity) hX hA2 hTφ

end TRS.Dev.TrackingFloor

namespace TRS

open TRS.Dev.TrackingFloor

theorem chk_tracking_floor (T d : ℕ) (hT : 8 ≤ T) (hd : 0 < d) (η : ℝ) (hη : 0 ≤ η)
    (hηT : η * T ≤ 1 / 4) (hdη : (d : ℝ) * η ≤ 1 / 8) (θ₀ : Vector d) :
    ∀ (B : ℕ) (s : RandomSeed) (π : ReleasePolicy s T d B), IsCausal π →
      ENNReal.ofReal ((2 : ℝ) ^ (-13 : ℤ) * T * trackingRate T d η) ≤
        driftWorstRisk θ₀ 0 η π := by
  intro B s π hπ
  rcases hη.eq_or_lt with h0 | hpos
  · subst h0
    have : trackingRate T d 0 = 0 := by
      unfold trackingRate
      simp [Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0)]
    rw [this]; simp
  · obtain ⟨w, K, hw2, hK, hs, hx, hnum⟩ := final_numeric T d hT hd η hpos hdη
    refine le_trans (ENNReal.ofReal_le_ofReal (hnum _ (four_card_goodSet w hw2))) ?_
    exact main_lb θ₀ hd π hπ w K hw2 hK η hη hs hx

end TRS

end
end

theorem solution : type_of% @TRS.chk_tracking_floor := @TRS.chk_tracking_floor
