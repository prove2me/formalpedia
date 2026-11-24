-- Prove2me | solution 1 for PhiSobBayes.eq_46_posterior_averaging
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T05:23:14.393309+00:00
-- url     : https://prove2.me/submissions/2a1ec458-288b-4c22-8d63-ea8aa5a2ad2e

import Mathlib
import Definitions.Def_PhiSobBayes_gamJoint
import Definitions.Def_PhiSobBayes_gamObs
import Definitions.Def_PhiSobBayes_posterior

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal ContDiff

theorem PSB46_lintegral_fin_prod {n : ℕ} (μ : Fin n → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (f : Fin n → ℝ → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n n_ih =>
      calc
        _ = ∫⁻ x : ℝ × (Fin n → ℝ), f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi (fun i ↦ μ i.succ))) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, Fin.cons_zero]
          rfl
        _ = (∫⁻ x, f 0 x ∂μ 0) * ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂(μ i.succ) := by
          rw [← n_ih (fun i => μ i.succ) (fun i => f i.succ) (fun i => hf _),
            ← lintegral_prod_mul (hf 0).aemeasurable]
          exact Finset.aemeasurable_fun_prod _ (fun (i : Fin n) _ => ((hf i.succ).comp (measurable_pi_apply i)).aemeasurable)
        _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]

theorem PSB46_pi_gaussianReal (n : ℕ) :
    Measure.pi (fun _ : Fin n => gaussianReal 0 1) =
      volume.withDensity (fun x => ∏ i, gaussianPDF 0 1 (x i)) := by
  refine Measure.pi_eq (μ := fun _ : Fin n => gaussianReal 0 1) fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), volume_pi, Measure.restrict_pi_pi,
    PSB46_lintegral_fin_prod _ _ (fun _ => measurable_gaussianPDF 0 1)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero, withDensity_apply _ (hs i)]

theorem PSB46_prod_gaussianPDF (n : ℕ) (x : Fin n → ℝ) :
    ∏ i, gaussianPDF 0 1 (x i) = ENNReal.ofReal ((2 * Real.pi) ^ (-(n : ℝ) / 2) *
      Real.exp (-‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n))‖ ^ 2 / 2)) := by
  simp only [gaussianPDF, gaussianPDFReal]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)]
  congr 1
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    ← Real.exp_sum, EuclideanSpace.norm_sq_eq]
  congr 1
  · rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (by positivity), ← Real.rpow_mul_natCast (by positivity)]
    congr 1
    · simp
    · ring
  · congr 1
    rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Real.norm_eq_abs, sq_abs, neg_div]

theorem PSB46_stdGaussian_eq_withDensity (n : ℕ) :
    stdGaussian (EuclideanSpace ℝ (Fin n)) = volume.withDensity (fun g =>
      ENNReal.ofReal ((2 * Real.pi) ^ (-(n : ℝ) / 2) * Real.exp (-‖g‖ ^ 2 / 2))) := by
  rw [← map_pi_eq_stdGaussian, PSB46_pi_gaussianReal]
  ext s hs
  rw [Measure.map_apply (WithLp.measurable_toLp 2 _) hs,
    withDensity_apply _ (hs.preimage (WithLp.measurable_toLp 2 _)), withDensity_apply _ hs,
    ← (PiLp.volume_preserving_toLp (Fin n)).setLIntegral_comp_preimage_emb
      (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurableEmbedding]
  congr 1
  funext x
  exact PSB46_prod_gaussianPDF n x

theorem PSB46_gamJoint_lintegral {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (t : ℝ)
    (g : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ p, g p ∂(PhiSobBayes.gamJoint μ t) =
      ∫⁻ y, ∫⁻ x, g (x, y) * ENNReal.ofReal ((2 * Real.pi) ^ (-(n : ℝ) / 2) *
        Real.exp (-‖y - Real.sqrt t • x‖ ^ 2 / 2)) ∂μ ∂volume := by
  have hF : Measurable (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (p.1, Real.sqrt t • p.1 + p.2)) := by fun_prop
  have hφ : Measurable (fun g : EuclideanSpace ℝ (Fin n) =>
      ENNReal.ofReal ((2 * Real.pi) ^ (-(n : ℝ) / 2) * Real.exp (-‖g‖ ^ 2 / 2))) := by fun_prop
  unfold PhiSobBayes.gamJoint
  rw [lintegral_map hg hF, lintegral_prod _ (by fun_prop),
    PSB46_stdGaussian_eq_withDensity]
  have key : ∀ x : EuclideanSpace ℝ (Fin n),
      ∫⁻ z, g (x, Real.sqrt t • x + z) ∂(volume.withDensity (fun g : EuclideanSpace ℝ (Fin n) =>
        ENNReal.ofReal ((2 * Real.pi) ^ (-(n : ℝ) / 2) * Real.exp (-‖g‖ ^ 2 / 2)))) =
      ∫⁻ y, g (x, y) * ENNReal.ofReal ((2 * Real.pi) ^ (-(n : ℝ) / 2) *
        Real.exp (-‖y - Real.sqrt t • x‖ ^ 2 / 2)) := by
    intro x
    rw [lintegral_withDensity_eq_lintegral_mul _ hφ (by fun_prop)]
    refine Eq.trans ?_ (lintegral_add_left_eq_self (fun y => g (x, y) *
      ENNReal.ofReal ((2 * Real.pi) ^ (-(n : ℝ) / 2) *
        Real.exp (-‖y - Real.sqrt t • x‖ ^ 2 / 2))) (Real.sqrt t • x))
    congr 1
    funext z
    simp [mul_comm]
  simp_rw [key]
  exact lintegral_lintegral_swap (by fun_prop)

theorem PSB46_integrable_kernel {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (t : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    Integrable (fun x => Real.exp (-‖y - Real.sqrt t • x‖ ^ 2 / 2)) μ := by
  refine Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖y - Real.sqrt t • x‖])

theorem PSB46_normalizer_pos {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (t : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    0 < ∫ x, Real.exp (-‖y - Real.sqrt t • x‖ ^ 2 / 2) ∂μ :=
  integral_exp_pos (PSB46_integrable_kernel μ t y)

theorem PSB46_measurable_normalizer {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (t : ℝ) :
    Measurable (fun y : EuclideanSpace ℝ (Fin n) =>
      ∫ x, Real.exp (-‖y - Real.sqrt t • x‖ ^ 2 / 2) ∂μ) := by
  refine StronglyMeasurable.measurable ?_
  refine StronglyMeasurable.integral_prod_right
    (f := fun (y x : EuclideanSpace ℝ (Fin n)) => Real.exp (-‖y - Real.sqrt t • x‖ ^ 2 / 2)) ?_
  exact Continuous.stronglyMeasurable (by fun_prop)

theorem PSB46_lintegral_kernel {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (t : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    ∫⁻ x, ENNReal.ofReal ((2 * Real.pi) ^ (-(n : ℝ) / 2) *
        Real.exp (-‖y - Real.sqrt t • x‖ ^ 2 / 2)) ∂μ =
      ENNReal.ofReal ((2 * Real.pi) ^ (-(n : ℝ) / 2) *
        ∫ x, Real.exp (-‖y - Real.sqrt t • x‖ ^ 2 / 2) ∂μ) := by
  rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal
    ((PSB46_integrable_kernel μ t y).const_mul _)
    (Filter.Eventually.of_forall fun x => by positivity)]

theorem PSB46_gamObs_eq_map {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) (t : ℝ) :
    PhiSobBayes.gamObs μ t = (PhiSobBayes.gamJoint μ t).map Prod.snd := by
  unfold PhiSobBayes.gamObs PhiSobBayes.gamJoint
  rw [Measure.map_map measurable_snd (by fun_prop)]
  rfl

theorem PSB46_gamObs_lintegral {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (t : ℝ) (h : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ y, h y ∂(PhiSobBayes.gamObs μ t) =
      ∫⁻ y, h y * ENNReal.ofReal ((2 * Real.pi) ^ (-(n : ℝ) / 2) *
        ∫ x, Real.exp (-‖y - Real.sqrt t • x‖ ^ 2 / 2) ∂μ) := by
  rw [PSB46_gamObs_eq_map, lintegral_map hh measurable_snd,
    PSB46_gamJoint_lintegral μ t (fun p => h p.2) (hh.comp measurable_snd)]
  congr 1
  funext y
  dsimp only
  rw [lintegral_const_mul _ (by fun_prop), PSB46_lintegral_kernel]

/-- Density of the observation law with respect to Lebesgue measure. -/
theorem PSB46_gamObs_eq_withDensity {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (t : ℝ) :
    PhiSobBayes.gamObs μ t = volume.withDensity (fun y => ENNReal.ofReal
      ((2 * Real.pi) ^ (-(n : ℝ) / 2) * ∫ x, Real.exp (-‖y - Real.sqrt t • x‖ ^ 2 / 2) ∂μ)) := by
  ext B hB
  rw [withDensity_apply _ hB, ← lintegral_indicator_one hB,
    PSB46_gamObs_lintegral μ t _ (measurable_one.indicator hB), ← lintegral_indicator hB]
  congr 1
  funext y
  by_cases hy : y ∈ B <;> simp [hy]

/-- Functional form of the disintegration of the planted model. -/
theorem PSB46_gamJoint_lintegral_posterior {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (t : ℝ)
    (g : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ p, g p ∂(PhiSobBayes.gamJoint μ t) =
      ∫⁻ y, ∫⁻ x, g (x, y) ∂(PhiSobBayes.posterior μ t y) ∂(PhiSobBayes.gamObs μ t) := by
  rw [PSB46_gamJoint_lintegral μ t g hg, PSB46_gamObs_eq_withDensity,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      ((PSB46_measurable_normalizer μ t).const_mul _).ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  congr 1
  funext y
  have hZ := PSB46_normalizer_pos μ t y
  unfold PhiSobBayes.posterior
  rw [Pi.mul_apply, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext x
  simp only [Pi.mul_apply]
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity), mul_comm (g (x, y))]
  congr 2
  rw [mul_assoc, mul_div_assoc', mul_div_cancel_left₀ _ hZ.ne']

theorem PSB46_gamJoint_rect {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (t : ℝ) (A B : Set (EuclideanSpace ℝ (Fin n)))
    (hA : MeasurableSet A) (hB : MeasurableSet B) :
    PhiSobBayes.gamJoint μ t (A ×ˢ B) =
      ∫⁻ y in B, PhiSobBayes.posterior μ t y A ∂(PhiSobBayes.gamObs μ t) := by
  rw [← lintegral_indicator_one (hA.prod hB),
    PSB46_gamJoint_lintegral_posterior μ t _ (measurable_one.indicator (hA.prod hB)),
    ← lintegral_indicator hB]
  congr 1
  funext y
  by_cases hy : y ∈ B
  · rw [Set.indicator_of_mem hy, ← lintegral_indicator_one hA]
    congr 1
    funext x
    by_cases hx : x ∈ A <;> simp [hx, hy, Set.indicator]
  · simp [hy, Set.indicator]

theorem PSB46_gamJoint_fst {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure μ] (t : ℝ) (A : Set (EuclideanSpace ℝ (Fin n)))
    (hA : MeasurableSet A) :
    PhiSobBayes.gamJoint μ t (A ×ˢ Set.univ) = μ A := by
  unfold PhiSobBayes.gamJoint
  rw [Measure.map_apply (by fun_prop) (hA.prod MeasurableSet.univ)]
  have : (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
      (p.1, Real.sqrt t • p.1 + p.2)) ⁻¹' (A ×ˢ Set.univ) = A ×ˢ Set.univ := by
    ext p; simp
  rw [this, Measure.prod_prod, measure_univ, mul_one]

theorem solution {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (t : ℝ) (ht : 0 < t) :
    (∀ A B : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A → MeasurableSet B →
      PhiSobBayes.gamJoint μ t (A ×ˢ B) =
        ∫⁻ y in B, PhiSobBayes.posterior μ t y A ∂(PhiSobBayes.gamObs μ t)) ∧
    (∀ A : Set (EuclideanSpace ℝ (Fin n)), MeasurableSet A →
      ∫⁻ y, PhiSobBayes.posterior μ t y A ∂(PhiSobBayes.gamObs μ t) = μ A) := by
  refine ⟨fun A B hA hB => PSB46_gamJoint_rect μ t A B hA hB, fun A hA => ?_⟩
  rw [← PSB46_gamJoint_fst μ t A hA, PSB46_gamJoint_rect μ t A Set.univ hA MeasurableSet.univ,
    Measure.restrict_univ]
