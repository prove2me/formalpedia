-- Prove2me | solution 1 for ShadowTomography.QuantumLB.eq_2
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-25T03:22:59.932233+00:00
-- url     : https://prove2.me/submissions/583572fc-c53a-4921-b4dc-6f6d2bd12041

import Mathlib
import Definitions.Def_ShadowTomography_QuantumLB_IsHalfProjector
import Definitions.Def_ShadowTomography_QuantumLB_rhoState

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Matrix
open scoped ComplexOrder

namespace E2C1

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The rotation `(x, y) ↦ (x sin θ + y cos θ, x cos θ - y sin θ)` of `E × E`. -/
noncomputable def rotL (θ : ℝ) : E × E →L[ℝ] E × E :=
  (Real.sin θ • ContinuousLinearMap.fst ℝ E E + Real.cos θ • ContinuousLinearMap.snd ℝ E E).prod
    (Real.cos θ • ContinuousLinearMap.fst ℝ E E - Real.sin θ • ContinuousLinearMap.snd ℝ E E)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma rotL_apply (θ : ℝ) (p : E × E) :
    rotL θ p = (Real.sin θ • p.1 + Real.cos θ • p.2, Real.cos θ • p.1 - Real.sin θ • p.2) := rfl

omit [MeasurableSpace E] [BorelSpace E] in
lemma dual_norm_rot (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) (L1 L2 : StrongDual ℝ E) :
    ‖a • L1 + b • L2‖ ^ 2 + ‖b • L1 - a • L2‖ ^ 2 = ‖L1‖ ^ 2 + ‖L2‖ ^ 2 := by
  have := FiniteDimensional.complete ℝ E
  obtain ⟨v1, rfl⟩ := (InnerProductSpace.toDual ℝ E).surjective L1
  obtain ⟨v2, rfl⟩ := (InnerProductSpace.toDual ℝ E).surjective L2
  have e1 : a • InnerProductSpace.toDual ℝ E v1 + b • InnerProductSpace.toDual ℝ E v2
      = InnerProductSpace.toDual ℝ E (a • v1 + b • v2) := by simp
  have e2 : b • InnerProductSpace.toDual ℝ E v1 - a • InnerProductSpace.toDual ℝ E v2
      = InnerProductSpace.toDual ℝ E (b • v1 - a • v2) := by simp
  rw [e1, e2]
  simp only [LinearIsometryEquiv.norm_map]
  rw [norm_add_sq_real, norm_sub_sq_real, norm_smul, norm_smul, norm_smul, norm_smul,
    real_inner_smul_left, real_inner_smul_right, real_inner_smul_left, real_inner_smul_right]
  simp only [Real.norm_eq_abs, mul_pow, sq_abs]
  linear_combination (‖v1‖ ^ 2 + ‖v2‖ ^ 2) * hab

/-- Rotation invariance of the product standard Gaussian. -/
lemma rot_inv (θ : ℝ) :
    ((stdGaussian E).prod (stdGaussian E)).map (rotL θ) = (stdGaussian E).prod (stdGaussian E) := by
  have := FiniteDimensional.complete ℝ E
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_map, charFunDual_prod, charFunDual_prod, charFunDual_stdGaussian,
    charFunDual_stdGaussian, charFunDual_stdGaussian, charFunDual_stdGaussian,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  set L1 := L.comp (ContinuousLinearMap.inl ℝ E E)
  set L2 := L.comp (ContinuousLinearMap.inr ℝ E E)
  have h1 : (L.comp (rotL θ)).comp (ContinuousLinearMap.inl ℝ E E)
      = Real.sin θ • L1 + Real.cos θ • L2 := by
    ext x
    simp only [L1, L2, ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.inr_apply, smul_eq_mul, rotL_apply]
    have e : ((Real.sin θ • x + Real.cos θ • (0 : E), Real.cos θ • x - Real.sin θ • (0 : E)) : E × E)
        = Real.sin θ • (x, (0 : E)) + Real.cos θ • ((0 : E), x) := by ext <;> simp
    rw [e, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have h2 : (L.comp (rotL θ)).comp (ContinuousLinearMap.inr ℝ E E)
      = Real.cos θ • L1 - Real.sin θ • L2 := by
    ext x
    simp only [L1, L2, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.inr_apply, smul_eq_mul, rotL_apply]
    have e : ((Real.sin θ • (0 : E) + Real.cos θ • x, Real.cos θ • (0 : E) - Real.sin θ • x) : E × E)
        = Real.cos θ • (x, (0 : E)) - Real.sin θ • ((0 : E), x) := by ext <;> simp
    rw [e, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [h1, h2]
  have key := dual_norm_rot (Real.sin θ) (Real.cos θ) (Real.sin_sq_add_cos_sq θ) L1 L2
  have keyC : ((‖Real.sin θ • L1 + Real.cos θ • L2‖ : ℝ) : ℂ) ^ 2
      + ((‖Real.cos θ • L1 - Real.sin θ • L2‖ : ℝ) : ℂ) ^ 2
      = ((‖L1‖ : ℝ) : ℂ) ^ 2 + ((‖L2‖ : ℝ) : ℂ) ^ 2 := by exact_mod_cast key
  linear_combination (-1 / 2 : ℂ) * keyC

omit [FiniteDimensional ℝ E] in
lemma map_dual_stdGaussian [FiniteDimensional ℝ E] (ℓ : StrongDual ℝ E) :
    (stdGaussian E).map ℓ = gaussianReal 0 (‖ℓ‖ ^ 2).toNNReal := by
  rw [IsGaussian.map_eq_gaussianReal ℓ, integral_strongDual_stdGaussian,
    variance_dual_stdGaussian]

lemma lintegral_exp_dual (ℓ : StrongDual ℝ E) (c : ℝ) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (c * ℓ y)) ∂(stdGaussian E)
      = ENNReal.ofReal (Real.exp (c ^ 2 * ‖ℓ‖ ^ 2 / 2)) := by
  have hm : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (c * x))) := by fun_prop
  rw [← lintegral_map hm ℓ.continuous.measurable, map_dual_stdGaussian,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_exp_mul_gaussianReal c)
      (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)]
  congr 1
  have h2 := congrFun (mgf_id_gaussianReal (μ := 0) (v := (‖ℓ‖ ^ 2).toNNReal)) c
  rw [mgf] at h2
  simp only [id] at h2
  rw [h2, Real.coe_toNNReal _ (by positivity)]
  congr 1; ring

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The rotation `(x, y) ↦ (x sin θ + y cos θ, x cos θ - y sin θ)` of `V × V`. -/
noncomputable def rotV (θ : ℝ) : V × V →L[ℝ] V × V :=
  (Real.sin θ • ContinuousLinearMap.fst ℝ V V + Real.cos θ • ContinuousLinearMap.snd ℝ V V).prod
    (Real.cos θ • ContinuousLinearMap.fst ℝ V V - Real.sin θ • ContinuousLinearMap.snd ℝ V V)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma rotV_apply (θ : ℝ) (p : V × V) :
    rotV θ p = (Real.sin θ • p.1 + Real.cos θ • p.2, Real.cos θ • p.1 - Real.sin θ • p.2) := rfl

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma rotV_cont (p : V × V) : Continuous (fun θ : ℝ => rotV θ p) := by
  show Continuous (fun θ : ℝ =>
    (Real.sin θ • p.1 + Real.cos θ • p.2, Real.cos θ • p.1 - Real.sin θ • p.2))
  exact continuous_prodMk.2 ⟨by fun_prop, by fun_prop⟩

/-- Directional derivative of `f` along the rotation path. -/
noncomputable def Dth (f : V → ℝ) (θ : ℝ) (p : V × V) : ℝ :=
  fderiv ℝ f (rotV θ p).1 (rotV θ p).2

lemma measurable_pairing (f : V → ℝ) : Measurable (fun q : V × V => fderiv ℝ f q.1 q.2) :=
  isBoundedBilinearMap_apply.continuous.measurable2
    ((measurable_fderiv ℝ f).comp measurable_fst) measurable_snd

lemma lintegral_Dth_le (γ : Measure V) [IsProbabilityMeasure γ]
    (hrot : ∀ θ, (γ.prod γ).map (rotV θ) = γ.prod γ)
    (hmgf : ∀ (ℓ : StrongDual ℝ V) (c : ℝ),
      ∫⁻ v, ENNReal.ofReal (Real.exp (c * ℓ v)) ∂γ ≤ ENNReal.ofReal (Real.exp (c ^ 2 * ‖ℓ‖ ^ 2 / 2)))
    (f : V → ℝ) (L : ℝ) (hL : ∀ x, ‖fderiv ℝ f x‖ ≤ L) (c θ : ℝ) :
    ∫⁻ p, ENNReal.ofReal (Real.exp (c * Dth f θ p)) ∂(γ.prod γ)
      ≤ ENNReal.ofReal (Real.exp (c ^ 2 * L ^ 2 / 2)) := by
  have hg : Measurable (fun q : V × V => ENNReal.ofReal (Real.exp (c * fderiv ℝ f q.1 q.2))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ((measurable_pairing f).const_mul c))
  calc ∫⁻ p, ENNReal.ofReal (Real.exp (c * Dth f θ p)) ∂(γ.prod γ)
      = ∫⁻ q, ENNReal.ofReal (Real.exp (c * fderiv ℝ f q.1 q.2)) ∂((γ.prod γ).map (rotV θ)) := by
        rw [lintegral_map hg (rotV θ).continuous.measurable]; rfl
    _ = ∫⁻ x, ∫⁻ y, ENNReal.ofReal (Real.exp (c * fderiv ℝ f x y)) ∂γ ∂γ := by
        rw [hrot, lintegral_prod _ hg.aemeasurable]
    _ ≤ ∫⁻ x, ENNReal.ofReal (Real.exp (c ^ 2 * L ^ 2 / 2)) ∂γ := by
        refine lintegral_mono fun x => (hmgf (fderiv ℝ f x) c).trans ?_
        apply ENNReal.ofReal_le_ofReal
        apply Real.exp_le_exp.2
        have h0 : 0 ≤ ‖fderiv ℝ f x‖ := norm_nonneg _
        have h1 := hL x
        have h2 : ‖fderiv ℝ f x‖ ^ 2 ≤ L ^ 2 := by nlinarith
        have hc : 0 ≤ c ^ 2 := sq_nonneg c
        nlinarith
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

lemma Dth_bound (f : V → ℝ) (L : ℝ) (hL : ∀ x, ‖fderiv ℝ f x‖ ≤ L) (θ : ℝ) (p : V × V) :
    ‖Dth f θ p‖ ≤ L * (‖p.1‖ + ‖p.2‖) := by
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  have hw : ‖(rotV θ p).2‖ ≤ ‖p.1‖ + ‖p.2‖ := by
    rw [rotV_apply]
    calc ‖Real.cos θ • p.1 - Real.sin θ • p.2‖ ≤ ‖Real.cos θ • p.1‖ + ‖Real.sin θ • p.2‖ :=
          norm_sub_le _ _
      _ = |Real.cos θ| * ‖p.1‖ + |Real.sin θ| * ‖p.2‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ 1 * ‖p.1‖ + 1 * ‖p.2‖ := by
          gcongr
          · exact Real.abs_cos_le_one θ
          · exact Real.abs_sin_le_one θ
      _ = _ := by ring
  calc ‖Dth f θ p‖ ≤ ‖fderiv ℝ f (rotV θ p).1‖ * ‖(rotV θ p).2‖ := (fderiv ℝ f _).le_opNorm _
    _ ≤ L * (‖p.1‖ + ‖p.2‖) := mul_le_mul (hL _) hw (norm_nonneg _) hL0

lemma ftc_rot (f : V → ℝ) (hf : Differentiable ℝ f) (L : ℝ) (hL : ∀ x, ‖fderiv ℝ f x‖ ≤ L)
    (p : V × V) :
    IntervalIntegrable (fun θ => Dth f θ p) volume 0 (Real.pi / 2) ∧
    ∫ θ in (0 : ℝ)..(Real.pi / 2), Dth f θ p = f p.1 - f p.2 := by
  have hγ : ∀ θ, HasDerivAt (fun θ => (rotV θ p).1) (rotV θ p).2 θ := by
    intro θ
    have := ((Real.hasDerivAt_sin θ).smul_const p.1).add ((Real.hasDerivAt_cos θ).smul_const p.2)
    convert this using 1
    · funext y; simp [rotV_apply]
    · simp only [rotV_apply, neg_smul, sub_eq_add_neg]
  have hD : ∀ θ, HasDerivAt (fun θ => f (rotV θ p).1) (Dth f θ p) θ := fun θ =>
    (hf _).hasFDerivAt.comp_hasDerivAt θ (hγ θ)
  have hmeas : Measurable (fun θ : ℝ => Dth f θ p) :=
    (measurable_pairing f).comp (rotV_cont p).measurable
  have hint : IntervalIntegrable (fun θ => Dth f θ p) volume 0 (Real.pi / 2) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)]
    exact Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun θ => Dth_bound f L hL θ p)
  refine ⟨hint, ?_⟩
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hD θ) hint]
  simp [rotV_apply]

lemma jensen_rot (f : V → ℝ) (hf : Differentiable ℝ f) (L : ℝ) (hL : ∀ x, ‖fderiv ℝ f x‖ ≤ L)
    (lam : ℝ) (p : V × V) :
    ENNReal.ofReal (Real.exp (lam * (f p.1 - f p.2))) ≤
      ENNReal.ofReal (2 / Real.pi) * ∫⁻ θ in Set.Ioc 0 (Real.pi / 2),
        ENNReal.ofReal (Real.exp (lam * (Real.pi / 2) * Dth f θ p)) := by
  obtain ⟨hint, hftc⟩ := ftc_rot f hf L hL p
  have hpi : 0 < Real.pi / 2 := by positivity
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hpi.le] at hint
  rw [intervalIntegral.integral_of_le hpi.le] at hftc
  have hvol : volume (Set.Ioc (0 : ℝ) (Real.pi / 2)) = ENNReal.ofReal (Real.pi / 2) := by
    simp [Real.volume_Ioc]
  have hvr : volume.real (Set.Ioc (0 : ℝ) (Real.pi / 2)) = Real.pi / 2 := by
    rw [measureReal_def, hvol, ENNReal.toReal_ofReal hpi.le]
  have hmeas : Measurable (fun θ : ℝ => Dth f θ p) :=
    (measurable_pairing f).comp (rotV_cont p).measurable
  have hgi : IntegrableOn (fun θ => Real.exp (lam * (Real.pi / 2) * Dth f θ p))
      (Set.Ioc 0 (Real.pi / 2)) volume := by
    refine Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
      (Real.measurable_exp.comp (hmeas.const_mul _)).aestronglyMeasurable
      (M := Real.exp (|lam * (Real.pi / 2)| * (L * (‖p.1‖ + ‖p.2‖))))
      (Filter.Eventually.of_forall fun θ => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_exp.2
    calc lam * (Real.pi / 2) * Dth f θ p ≤ |lam * (Real.pi / 2) * Dth f θ p| := le_abs_self _
      _ = |lam * (Real.pi / 2)| * ‖Dth f θ p‖ := by rw [abs_mul, Real.norm_eq_abs]
      _ ≤ _ := mul_le_mul_of_nonneg_left (Dth_bound f L hL θ p) (abs_nonneg _)
  have hJ := ConvexOn.map_set_average_le convexOn_exp Real.continuous_exp.continuousOn
    isClosed_univ (μ := volume) (t := Set.Ioc (0 : ℝ) (Real.pi / 2))
    (f := fun θ => lam * (Real.pi / 2) * Dth f θ p) (by rw [hvol]; simp [hpi])
    (by rw [hvol]; simp) (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
    (hint.const_mul _) hgi
  simp only [setAverage_eq, hvr, smul_eq_mul] at hJ
  rw [integral_const_mul, hftc] at hJ
  have e : (Real.pi / 2)⁻¹ * (lam * (Real.pi / 2) * (f p.1 - f p.2)) = lam * (f p.1 - f p.2) := by
    field_simp
  rw [e] at hJ
  calc ENNReal.ofReal (Real.exp (lam * (f p.1 - f p.2)))
      ≤ ENNReal.ofReal ((Real.pi / 2)⁻¹ * ∫ θ in Set.Ioc 0 (Real.pi / 2),
          Real.exp (lam * (Real.pi / 2) * Dth f θ p)) := ENNReal.ofReal_le_ofReal hJ
    _ = ENNReal.ofReal (2 / Real.pi) * ENNReal.ofReal (∫ θ in Set.Ioc 0 (Real.pi / 2),
          Real.exp (lam * (Real.pi / 2) * Dth f θ p)) := by
        rw [ENNReal.ofReal_mul (by positivity)]; congr 2; field_simp
    _ = _ := by
        rw [ofReal_integral_eq_lintegral_ofReal hgi
          (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
lemma rotV_cont2 : Continuous (fun q : (V × V) × ℝ => rotV q.2 q.1) := by
  show Continuous (fun q : (V × V) × ℝ =>
    (Real.sin q.2 • q.1.1 + Real.cos q.2 • q.1.2, Real.cos q.2 • q.1.1 - Real.sin q.2 • q.1.2))
  exact continuous_prodMk.2 ⟨by fun_prop, by fun_prop⟩

lemma expmoment (γ : Measure V) [IsProbabilityMeasure γ]
    (hrot : ∀ θ, (γ.prod γ).map (rotV θ) = γ.prod γ)
    (hmgf : ∀ (ℓ : StrongDual ℝ V) (c : ℝ),
      ∫⁻ v, ENNReal.ofReal (Real.exp (c * ℓ v)) ∂γ ≤ ENNReal.ofReal (Real.exp (c ^ 2 * ‖ℓ‖ ^ 2 / 2)))
    (f : V → ℝ) (hf : Differentiable ℝ f) (L : ℝ) (hL : ∀ x, ‖fderiv ℝ f x‖ ≤ L)
    (M : ℝ) (hM : ∀ x, |f x| ≤ M) (lam : ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (lam * (f x - ∫ y, f y ∂γ))) ∂γ
      ≤ ENNReal.ofReal (Real.exp (lam ^ 2 * Real.pi ^ 2 * L ^ 2 / 8)) := by
  have hfm : Measurable f := hf.continuous.measurable
  have hfi : Integrable f γ := integrableOn_univ.1 (Measure.integrableOn_of_bounded
    (measure_ne_top γ _) hfm.aestronglyMeasurable (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hM x))
  have hpi : 0 < Real.pi / 2 := by positivity
  -- Jensen in the second variable
  have step1 : ∀ x, ENNReal.ofReal (Real.exp (lam * (f x - ∫ y, f y ∂γ)))
      ≤ ∫⁻ y, ENNReal.ofReal (Real.exp (lam * (f x - f y))) ∂γ := by
    intro x
    have hgi : Integrable (fun y => Real.exp (lam * (f x - f y))) γ :=
      integrableOn_univ.1 (Measure.integrableOn_of_bounded (M := Real.exp (|lam| * (2 * M)))
        (measure_ne_top γ _)
        (Real.measurable_exp.comp ((measurable_const.sub hfm).const_mul lam)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          apply Real.exp_le_exp.2
          have h1 := hM x
          have h2 := hM y
          calc lam * (f x - f y) ≤ |lam * (f x - f y)| := le_abs_self _
            _ = |lam| * |f x - f y| := abs_mul _ _
            _ ≤ |lam| * (2 * M) := by
                apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
                have := abs_sub (f x) (f y)
                linarith))
    have hJ := ConvexOn.map_integral_le convexOn_exp Real.continuous_exp.continuousOn
      isClosed_univ (μ := γ) (f := fun y => lam * (f x - f y))
      (Filter.Eventually.of_forall fun _ => Set.mem_univ _)
      ((integrable_const _ |>.sub hfi).const_mul lam) hgi
    rw [integral_const_mul, integral_sub (integrable_const _) hfi, integral_const] at hJ
    simp only [measureReal_def, measure_univ, ENNReal.toReal_one, one_smul] at hJ
    rw [← ofReal_integral_eq_lintegral_ofReal hgi
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_le_ofReal hJ
  have hmeasP : Measurable (fun p : V × V => ENNReal.ofReal (Real.exp (lam * (f p.1 - f p.2)))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (((hfm.comp measurable_fst).sub (hfm.comp measurable_snd)).const_mul lam))
  have hmeasT : Measurable (fun q : (V × V) × ℝ =>
      ENNReal.ofReal (Real.exp (lam * (Real.pi / 2) * Dth f q.2 q.1))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (((measurable_pairing f).comp rotV_cont2.measurable).const_mul _))
  calc ∫⁻ x, ENNReal.ofReal (Real.exp (lam * (f x - ∫ y, f y ∂γ))) ∂γ
      ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal (Real.exp (lam * (f x - f y))) ∂γ ∂γ := lintegral_mono step1
    _ = ∫⁻ p, ENNReal.ofReal (Real.exp (lam * (f p.1 - f p.2))) ∂(γ.prod γ) :=
        (lintegral_prod _ hmeasP.aemeasurable).symm
    _ ≤ ∫⁻ p, (ENNReal.ofReal (2 / Real.pi) * ∫⁻ θ in Set.Ioc 0 (Real.pi / 2),
          ENNReal.ofReal (Real.exp (lam * (Real.pi / 2) * Dth f θ p))) ∂(γ.prod γ) :=
        lintegral_mono fun p => jensen_rot f hf L hL lam p
    _ = ENNReal.ofReal (2 / Real.pi) * ∫⁻ p, (∫⁻ θ in Set.Ioc 0 (Real.pi / 2),
          ENNReal.ofReal (Real.exp (lam * (Real.pi / 2) * Dth f θ p))) ∂(γ.prod γ) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (2 / Real.pi) * ∫⁻ θ in Set.Ioc 0 (Real.pi / 2), ∫⁻ p,
          ENNReal.ofReal (Real.exp (lam * (Real.pi / 2) * Dth f θ p)) ∂(γ.prod γ) := by
        rw [lintegral_lintegral_swap hmeasT.aemeasurable]
    _ ≤ ENNReal.ofReal (2 / Real.pi) * ∫⁻ θ in Set.Ioc 0 (Real.pi / 2),
          ENNReal.ofReal (Real.exp ((lam * (Real.pi / 2)) ^ 2 * L ^ 2 / 2)) := by
        gcongr with θ
        exact lintegral_Dth_le γ hrot hmgf f L hL _ θ
    _ = ENNReal.ofReal (Real.exp (lam ^ 2 * Real.pi ^ 2 * L ^ 2 / 8)) := by
        rw [setLIntegral_const, Real.volume_Ioc, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        have e : (lam * (Real.pi / 2)) ^ 2 * L ^ 2 / 2 = lam ^ 2 * Real.pi ^ 2 * L ^ 2 / 8 := by ring
        rw [e, sub_zero]
        field_simp

lemma tail_one (γ : Measure V) [IsProbabilityMeasure γ]
    (hrot : ∀ θ, (γ.prod γ).map (rotV θ) = γ.prod γ)
    (hmgf : ∀ (ℓ : StrongDual ℝ V) (c : ℝ),
      ∫⁻ v, ENNReal.ofReal (Real.exp (c * ℓ v)) ∂γ ≤ ENNReal.ofReal (Real.exp (c ^ 2 * ‖ℓ‖ ^ 2 / 2)))
    (f : V → ℝ) (hf : Differentiable ℝ f) (L : ℝ) (hL : ∀ x, ‖fderiv ℝ f x‖ ≤ L)
    (M : ℝ) (hM : ∀ x, |f x| ≤ M) (hL0 : 0 < L) (t : ℝ) (ht : 0 < t) :
    γ {x | t ≤ f x - ∫ y, f y ∂γ}
      ≤ ENNReal.ofReal (Real.exp (-(2 * t ^ 2) / (Real.pi ^ 2 * L ^ 2))) := by
  set lam := 4 * t / (Real.pi ^ 2 * L ^ 2) with hlam
  have hlam0 : 0 < lam := by positivity
  set F := fun x => ENNReal.ofReal (Real.exp (lam * (f x - ∫ y, f y ∂γ))) with hF
  have hFm : Measurable F := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    ((hf.continuous.measurable.sub measurable_const).const_mul lam))
  have hmk := mul_meas_ge_le_lintegral (μ := γ) hFm (ENNReal.ofReal (Real.exp (lam * t)))
  have hsub : {x | t ≤ f x - ∫ y, f y ∂γ} ⊆
      {x | ENNReal.ofReal (Real.exp (lam * t)) ≤ F x} := by
    intro x hx
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hx hlam0.le))
  have hB := expmoment γ hrot hmgf f hf L hL M hM lam
  have h1 : ENNReal.ofReal (Real.exp (-(lam * t))) * ENNReal.ofReal (Real.exp (lam * t)) = 1 := by
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, neg_add_cancel, Real.exp_zero,
      ENNReal.ofReal_one]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hL' : L ≠ 0 := hL0.ne'
  calc γ {x | t ≤ f x - ∫ y, f y ∂γ}
      ≤ γ {x | ENNReal.ofReal (Real.exp (lam * t)) ≤ F x} := measure_mono hsub
    _ = ENNReal.ofReal (Real.exp (-(lam * t))) * (ENNReal.ofReal (Real.exp (lam * t)) *
          γ {x | ENNReal.ofReal (Real.exp (lam * t)) ≤ F x}) := by rw [← mul_assoc, h1, one_mul]
    _ ≤ ENNReal.ofReal (Real.exp (-(lam * t))) *
          ENNReal.ofReal (Real.exp (lam ^ 2 * Real.pi ^ 2 * L ^ 2 / 8)) := by
        gcongr; exact hmk.trans hB
    _ = _ := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2
        rw [hlam]; field_simp; ring

lemma tail_two (γ : Measure V) [IsProbabilityMeasure γ]
    (hrot : ∀ θ, (γ.prod γ).map (rotV θ) = γ.prod γ)
    (hmgf : ∀ (ℓ : StrongDual ℝ V) (c : ℝ),
      ∫⁻ v, ENNReal.ofReal (Real.exp (c * ℓ v)) ∂γ ≤ ENNReal.ofReal (Real.exp (c ^ 2 * ‖ℓ‖ ^ 2 / 2)))
    (f : V → ℝ) (hf : Differentiable ℝ f) (L : ℝ) (hL : ∀ x, ‖fderiv ℝ f x‖ ≤ L)
    (M : ℝ) (hM : ∀ x, |f x| ≤ M) (t : ℝ) (ht : 0 < t) :
    γ.real {x | t ≤ |f x - ∫ y, f y ∂γ|}
      ≤ 2 * Real.exp (-(2 * t ^ 2) / (Real.pi ^ 2 * L ^ 2)) := by
  have hL0' : 0 ≤ L := (norm_nonneg _).trans (hL 0)
  rcases hL0'.lt_or_eq with hL0 | hL0
  · have hA := tail_one γ hrot hmgf f hf L hL M hM hL0 t ht
    have hB := tail_one γ hrot hmgf (fun x => -f x) hf.neg L
      (fun x => by show ‖fderiv ℝ (-f) x‖ ≤ L; rw [fderiv_neg, norm_neg]; exact hL x) M (fun x => by rw [abs_neg]; exact hM x)
      hL0 t ht
    rw [integral_neg] at hB
    have hsub : {x | t ≤ |f x - ∫ y, f y ∂γ|} ⊆
        {x | t ≤ f x - ∫ y, f y ∂γ} ∪ {x | t ≤ -f x - -∫ y, f y ∂γ} := by
      intro x hx
      have hx' : t ≤ |f x - ∫ y, f y ∂γ| := hx
      rcases le_abs.1 hx' with h | h
      · exact Or.inl h
      · right; show t ≤ -f x - -∫ y, f y ∂γ; linarith
    have e1 : γ.real {x | t ≤ f x - ∫ y, f y ∂γ}
        ≤ Real.exp (-(2 * t ^ 2) / (Real.pi ^ 2 * L ^ 2)) :=
      ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le hA
    have e2 : γ.real {x | t ≤ -f x - -∫ y, f y ∂γ}
        ≤ Real.exp (-(2 * t ^ 2) / (Real.pi ^ 2 * L ^ 2)) :=
      ENNReal.toReal_le_of_le_ofReal (Real.exp_pos _).le hB
    calc γ.real {x | t ≤ |f x - ∫ y, f y ∂γ|}
        ≤ γ.real ({x | t ≤ f x - ∫ y, f y ∂γ} ∪ {x | t ≤ -f x - -∫ y, f y ∂γ}) :=
          measureReal_mono hsub
      _ ≤ γ.real {x | t ≤ f x - ∫ y, f y ∂γ} + γ.real {x | t ≤ -f x - -∫ y, f y ∂γ} :=
          measureReal_union_le _ _
      _ ≤ _ := by linarith
  · subst hL0
    have h1 : γ.real {x | t ≤ |f x - ∫ y, f y ∂γ|} ≤ 1 := by
      rw [measureReal_def]
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, div_zero,
      Real.exp_zero, mul_one]
    linarith

end General

section Inst

lemma hrot_of_char {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (γ : Measure V) [IsProbabilityMeasure γ]
    (Q : StrongDual ℝ V → ℝ) (hγ : ∀ ℓ, charFunDual γ ℓ = Complex.exp (-(Q ℓ : ℂ) / 2))
    (hQ : ∀ a b : ℝ, a ^ 2 + b ^ 2 = 1 → ∀ L1 L2 : StrongDual ℝ V,
      Q (a • L1 + b • L2) + Q (b • L1 - a • L2) = Q L1 + Q L2) (θ : ℝ) :
    (γ.prod γ).map (rotV θ) = γ.prod γ := by
  have := FiniteDimensional.complete ℝ V
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_map, charFunDual_prod, charFunDual_prod, hγ, hγ, hγ, hγ,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  set L1 := L.comp (ContinuousLinearMap.inl ℝ V V)
  set L2 := L.comp (ContinuousLinearMap.inr ℝ V V)
  have h1 : (L.comp (rotV θ)).comp (ContinuousLinearMap.inl ℝ V V)
      = Real.sin θ • L1 + Real.cos θ • L2 := by
    ext x
    simp only [L1, L2, ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.inr_apply, smul_eq_mul, rotV_apply]
    have e : ((Real.sin θ • x + Real.cos θ • (0 : V), Real.cos θ • x - Real.sin θ • (0 : V)) : V × V)
        = Real.sin θ • (x, (0 : V)) + Real.cos θ • ((0 : V), x) := by ext <;> simp
    rw [e, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  have h2 : (L.comp (rotV θ)).comp (ContinuousLinearMap.inr ℝ V V)
      = Real.cos θ • L1 - Real.sin θ • L2 := by
    ext x
    simp only [L1, L2, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.inl_apply,
      ContinuousLinearMap.inr_apply, smul_eq_mul, rotV_apply]
    have e : ((Real.sin θ • (0 : V) + Real.cos θ • x, Real.cos θ • (0 : V) - Real.sin θ • x) : V × V)
        = Real.cos θ • (x, (0 : V)) - Real.sin θ • ((0 : V), x) := by ext <;> simp
    rw [e, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  rw [h1, h2]
  have key := hQ _ _ (Real.sin_sq_add_cos_sq θ) L1 L2
  have keyC : ((Q (Real.sin θ • L1 + Real.cos θ • L2) : ℝ) : ℂ)
      + ((Q (Real.cos θ • L1 - Real.sin θ • L2) : ℝ) : ℂ)
      = ((Q L1 : ℝ) : ℂ) + ((Q L2 : ℝ) : ℂ) := by exact_mod_cast key
  linear_combination (-1 / 2 : ℂ) * keyC

lemma norm_comp_inl_inr (ℓ : StrongDual ℝ (E × E)) :
    ‖ℓ.comp (ContinuousLinearMap.inl ℝ E E)‖ ^ 2 + ‖ℓ.comp (ContinuousLinearMap.inr ℝ E E)‖ ^ 2
      ≤ ‖ℓ‖ ^ 2 := by
  have := FiniteDimensional.complete ℝ E
  obtain ⟨v1, hv1⟩ := (InnerProductSpace.toDual ℝ E).surjective (ℓ.comp (ContinuousLinearMap.inl ℝ E E))
  obtain ⟨v2, hv2⟩ := (InnerProductSpace.toDual ℝ E).surjective (ℓ.comp (ContinuousLinearMap.inr ℝ E E))
  have n1 : ‖ℓ.comp (ContinuousLinearMap.inl ℝ E E)‖ = ‖v1‖ := by
    rw [← hv1, LinearIsometryEquiv.norm_map]
  have n2 : ‖ℓ.comp (ContinuousLinearMap.inr ℝ E E)‖ = ‖v2‖ := by
    rw [← hv2, LinearIsometryEquiv.norm_map]
  rw [n1, n2]
  have hval : ℓ (v1, v2) = ‖v1‖ ^ 2 + ‖v2‖ ^ 2 := by
    have e : ((v1, v2) : E × E) = (v1, (0 : E)) + ((0 : E), v2) := by ext <;> simp
    have a1 : ℓ (v1, (0 : E)) = ‖v1‖ ^ 2 := by
      have := congrArg (fun g : StrongDual ℝ E => g v1) hv1
      simp only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.inl_apply] at this
      rw [← this, real_inner_self_eq_norm_sq]
    have a2 : ℓ ((0 : E), v2) = ‖v2‖ ^ 2 := by
      have := congrArg (fun g : StrongDual ℝ E => g v2) hv2
      simp only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.inr_apply] at this
      rw [← this, real_inner_self_eq_norm_sq]
    rw [e, map_add, a1, a2]
  set S := ‖v1‖ ^ 2 + ‖v2‖ ^ 2 with hS
  set N := ‖ℓ‖
  set mx := max ‖v1‖ ‖v2‖
  have hN : 0 ≤ N := norm_nonneg ℓ
  have hmx : 0 ≤ mx := le_max_of_le_left (norm_nonneg v1)
  have hS0 : 0 ≤ S := by positivity
  have hmS : mx ^ 2 ≤ S := by
    rcases le_total ‖v1‖ ‖v2‖ with h | h
    · rw [show mx = ‖v2‖ from max_eq_right h]; nlinarith [sq_nonneg ‖v1‖]
    · rw [show mx = ‖v1‖ from max_eq_left h]; nlinarith [sq_nonneg ‖v2‖]
  have hle : S ≤ N * mx := by
    rw [← hval]
    calc ℓ (v1, v2) ≤ |ℓ (v1, v2)| := le_abs_self _
      _ = ‖ℓ (v1, v2)‖ := (Real.norm_eq_abs _).symm
      _ ≤ N * ‖((v1, v2) : E × E)‖ := ℓ.le_opNorm _
      _ = N * mx := by rw [Prod.norm_mk]
  have hsq : S * S ≤ N ^ 2 * S := by
    have := mul_le_mul hle hle hS0 (mul_nonneg hN hmx)
    nlinarith [mul_le_mul_of_nonneg_left hmS (sq_nonneg N)]
  rcases hS0.lt_or_eq with hpos | hz
  · exact le_of_mul_le_mul_right (by linarith) hpos
  · rw [← hz]; positivity

lemma charFunDual_prod_std (ℓ : StrongDual ℝ (E × E)) :
    charFunDual ((stdGaussian E).prod (stdGaussian E)) ℓ
      = Complex.exp (-((‖ℓ.comp (ContinuousLinearMap.inl ℝ E E)‖ ^ 2
          + ‖ℓ.comp (ContinuousLinearMap.inr ℝ E E)‖ ^ 2 : ℝ) : ℂ) / 2) := by
  rw [charFunDual_prod, charFunDual_stdGaussian, charFunDual_stdGaussian, ← Complex.exp_add]
  congr 1; push_cast; ring

lemma hrot_std2 (θ : ℝ) :
    (((stdGaussian E).prod (stdGaussian E)).prod ((stdGaussian E).prod (stdGaussian E))).map
        (rotV θ) = ((stdGaussian E).prod (stdGaussian E)).prod ((stdGaussian E).prod (stdGaussian E)) := by
  refine hrot_of_char _ (fun ℓ => ‖ℓ.comp (ContinuousLinearMap.inl ℝ E E)‖ ^ 2
          + ‖ℓ.comp (ContinuousLinearMap.inr ℝ E E)‖ ^ 2) charFunDual_prod_std ?_ θ
  intro a b hab L1 L2
  simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.sub_comp,
    ContinuousLinearMap.smul_comp]
  have k1 := dual_norm_rot a b hab (L1.comp (ContinuousLinearMap.inl ℝ E E))
    (L2.comp (ContinuousLinearMap.inl ℝ E E))
  have k2 := dual_norm_rot a b hab (L1.comp (ContinuousLinearMap.inr ℝ E E))
    (L2.comp (ContinuousLinearMap.inr ℝ E E))
  linear_combination k1 + k2

lemma hmgf_std2 (ℓ : StrongDual ℝ (E × E)) (c : ℝ) :
    ∫⁻ v, ENNReal.ofReal (Real.exp (c * ℓ v)) ∂((stdGaussian E).prod (stdGaussian E))
      ≤ ENNReal.ofReal (Real.exp (c ^ 2 * ‖ℓ‖ ^ 2 / 2)) := by
  set ℓ1 := ℓ.comp (ContinuousLinearMap.inl ℝ E E)
  set ℓ2 := ℓ.comp (ContinuousLinearMap.inr ℝ E E)
  have hsplit : ∀ v : E × E, ENNReal.ofReal (Real.exp (c * ℓ v))
      = ENNReal.ofReal (Real.exp (c * ℓ1 v.1)) * ENNReal.ofReal (Real.exp (c * ℓ2 v.2)) := by
    intro v
    have e : ℓ v = ℓ1 v.1 + ℓ2 v.2 := by
      have : v = (v.1, (0 : E)) + ((0 : E), v.2) := by ext <;> simp
      conv_lhs => rw [this]
      rw [map_add]; rfl
    rw [e, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, mul_add]
  have hm1 : Measurable (fun x : E => ENNReal.ofReal (Real.exp (c * ℓ1 x))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (ℓ1.continuous.measurable.const_mul c))
  have hm2 : Measurable (fun x : E => ENNReal.ofReal (Real.exp (c * ℓ2 x))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (ℓ2.continuous.measurable.const_mul c))
  simp_rw [hsplit]
  rw [lintegral_prod_mul hm1.aemeasurable hm2.aemeasurable, lintegral_exp_dual, lintegral_exp_dual,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.2
  have := norm_comp_inl_inr ℓ
  have hc : 0 ≤ c ^ 2 := sq_nonneg c
  nlinarith

/-- C1 with a boundedness hypothesis. -/
def C1_gauss_conc : Prop :=
  ∀ (ι : Type) [Fintype ι]
    (f : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι → ℝ) (L : NNReal),
    Differentiable ℝ f → LipschitzWith L f → (∃ M : ℝ, ∀ p, |f p| ≤ M) → ∀ t : ℝ, 0 < t →
      ((stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ ι))).real
          {p | t ≤ |f p - ∫ q, f q ∂((stdGaussian (EuclideanSpace ℝ ι)).prod
              (stdGaussian (EuclideanSpace ℝ ι)))|}
        ≤ 2 * Real.exp (-(2 * t ^ 2) / (Real.pi ^ 2 * (L : ℝ) ^ 2))

theorem C1 : C1_gauss_conc := by
  intro ι _ f L hf hlip hM t ht
  obtain ⟨M, hM⟩ := hM
  exact tail_two ((stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ ι)))
    hrot_std2 hmgf_std2 f hf L (fun x => norm_fderiv_le_of_lipschitz ℝ hlip) M hM t ht

end Inst

end E2C1

namespace E2C4

lemma gauss_mom2 (v : NNReal) : ∫ x, x ^ 2 ∂(gaussianReal 0 v) = v := by
  have hv := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_of_integral_eq_zero (by fun_prop) (by simp [integral_id_gaussianReal])] at hv
  exact hv

lemma hasDerivAt_expq (c t : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (c * t ^ 2 / 2)) (c * t * Real.exp (c * t ^ 2 / 2)) t := by
  have := (((hasDerivAt_pow 2 t).const_mul c).div_const 2).exp
  convert this using 1; push_cast; ring

lemma gauss_mom4 (v : NNReal) : ∫ x, x ^ 4 ∂(gaussianReal 0 v) = 3 * (v : ℝ) ^ 2 := by
  have h0 : (0 : ℝ) ∈ interior (integrableExpSet id (gaussianReal 0 v)) := by
    simp [integrableExpSet_id_gaussianReal]
  have h := iteratedDeriv_mgf_zero h0 4
  rw [mgf_id_gaussianReal] at h
  set c : ℝ := (v : ℝ) with hc
  have e : (fun t : ℝ => Real.exp (0 * t + c * t ^ 2 / 2)) = fun t => Real.exp (c * t ^ 2 / 2) := by
    funext t; simp
  rw [e] at h
  have d1 : deriv (fun t : ℝ => Real.exp (c * t ^ 2 / 2)) = fun t => c * t * Real.exp (c * t ^ 2 / 2) := by
    funext t; exact (hasDerivAt_expq c t).deriv
  have d2 : deriv (fun t : ℝ => c * t * Real.exp (c * t ^ 2 / 2)) =
      fun t => (c + c ^ 2 * t ^ 2) * Real.exp (c * t ^ 2 / 2) := by
    funext t
    have hd : HasDerivAt (fun t : ℝ => c * t * Real.exp (c * t ^ 2 / 2))
        ((c + c ^ 2 * t ^ 2) * Real.exp (c * t ^ 2 / 2)) t := by
      have := ((hasDerivAt_id t).const_mul c).mul (hasDerivAt_expq c t)
      exact this.congr_deriv (by simp only [id, mul_one]; ring)
    exact hd.deriv
  have d3 : deriv (fun t : ℝ => (c + c ^ 2 * t ^ 2) * Real.exp (c * t ^ 2 / 2)) =
      fun t => (3 * c ^ 2 * t + c ^ 3 * t ^ 3) * Real.exp (c * t ^ 2 / 2) := by
    funext t
    have hd : HasDerivAt (fun t : ℝ => (c + c ^ 2 * t ^ 2) * Real.exp (c * t ^ 2 / 2))
        ((3 * c ^ 2 * t + c ^ 3 * t ^ 3) * Real.exp (c * t ^ 2 / 2)) t := by
      have := (((hasDerivAt_pow 2 t).const_mul (c ^ 2)).const_add c).mul (hasDerivAt_expq c t)
      exact this.congr_deriv (by push_cast; ring)
    exact hd.deriv
  have d4 : deriv (fun t : ℝ => (3 * c ^ 2 * t + c ^ 3 * t ^ 3) * Real.exp (c * t ^ 2 / 2)) =
      fun t => (3 * c ^ 2 + 6 * c ^ 3 * t ^ 2 + c ^ 4 * t ^ 4) * Real.exp (c * t ^ 2 / 2) := by
    funext t
    have hd : HasDerivAt (fun t : ℝ => (3 * c ^ 2 * t + c ^ 3 * t ^ 3) * Real.exp (c * t ^ 2 / 2))
        ((3 * c ^ 2 + 6 * c ^ 3 * t ^ 2 + c ^ 4 * t ^ 4) * Real.exp (c * t ^ 2 / 2)) t := by
      have := (((hasDerivAt_id t).const_mul (3 * c ^ 2)).add
        ((hasDerivAt_pow 3 t).const_mul (c ^ 3))).mul (hasDerivAt_expq c t)
      exact this.congr_deriv (by simp only [id, Pi.add_apply]; push_cast; ring)
    exact hd.deriv
  simp only [iteratedDeriv_succ, iteratedDeriv_zero, d1, d2, d3, d4] at h
  rw [show (∫ x, x ^ 4 ∂(gaussianReal 0 v)) = ∫ x, (id ^ 4) x ∂(gaussianReal 0 v) from rfl, ← h]
  simp

variable {ι : Type} [Fintype ι] [DecidableEq ι]

lemma coord_map (a : ι) :
    (stdGaussian (EuclideanSpace ℝ ι)).map (fun z : EuclideanSpace ℝ ι => z a) = gaussianReal 0 1 := by
  rw [← map_pi_eq_stdGaussian, Measure.map_map (by fun_prop) (by fun_prop)]
  exact (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) a).map_eq

lemma intg_coord (a : ι) (g : ℝ → ℝ) (hg : Measurable g) (hi : Integrable g (gaussianReal 0 1)) :
    Integrable (fun z : EuclideanSpace ℝ ι => g (z a)) (stdGaussian (EuclideanSpace ℝ ι)) := by
  rw [← coord_map a, integrable_map_measure hg.aestronglyMeasurable (by fun_prop)] at hi
  exact hi

lemma int_coord (a : ι) (g : ℝ → ℝ) (hg : Measurable g) :
    ∫ z : EuclideanSpace ℝ ι, g (z a) ∂(stdGaussian (EuclideanSpace ℝ ι)) = ∫ t, g t ∂(gaussianReal 0 1) := by
  rw [← coord_map a, integral_map (by fun_prop) hg.aestronglyMeasurable]

lemma intg_pow (a : ι) (n : ℕ) :
    Integrable (fun z : EuclideanSpace ℝ ι => z a ^ n) (stdGaussian (EuclideanSpace ℝ ι)) := by
  refine intg_coord a (fun t => t ^ n) (by fun_prop) ?_
  have h := (memLp_id_gaussianReal (μ := 0) (v := 1) n).integrable_norm_pow'
  refine h.mono' (by fun_prop) (Filter.Eventually.of_forall fun t => ?_)
  simp [norm_pow]

lemma abs4 (a b c d : ℝ) : |a * b * c * d| ≤ a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4 := by
  have h1 : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b, abs_nonneg a, abs_nonneg b]
  have h2 : |c * d| ≤ (c ^ 2 + d ^ 2) / 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|c| - |d|), sq_abs c, sq_abs d, abs_nonneg c, abs_nonneg d]
  rw [show a * b * c * d = (a * b) * (c * d) by ring, abs_mul]
  have := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  nlinarith [sq_nonneg (a ^ 2 + b ^ 2 - (c ^ 2 + d ^ 2)), sq_nonneg (a ^ 2 - b ^ 2),
    sq_nonneg (c ^ 2 - d ^ 2)]

lemma intg_mono4 (a b c d : ι) :
    Integrable (fun z : EuclideanSpace ℝ ι => z a * z b * z c * z d)
      (stdGaussian (EuclideanSpace ℝ ι)) := by
  refine ((((intg_pow a 4).add (intg_pow b 4)).add (intg_pow c 4)).add (intg_pow d 4)).mono'
    (by fun_prop) (Filter.Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]
  exact abs4 _ _ _ _

/-- Coordinatewise sign change, an isometry. -/
noncomputable def signE (ε : ι → ℝ) (hε : ∀ p, ε p * ε p = 1) :
    EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι where
  toFun z := WithLp.toLp 2 (fun p => ε p * z p)
  invFun z := WithLp.toLp 2 (fun p => ε p * z p)
  map_add' x y := by ext p; simp [mul_add]
  map_smul' c x := by ext p; simp; ring
  left_inv z := by ext p; simp [← mul_assoc, hε]
  right_inv z := by ext p; simp [← mul_assoc, hε]
  norm_map' z := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Real.norm_eq_abs, sq_abs, PiLp.toLp_apply, LinearEquiv.coe_mk, LinearMap.coe_mk,
      AddHom.coe_mk]
    have := hε p
    rw [mul_pow]; nlinarith

lemma signE_apply (ε : ι → ℝ) (hε : ∀ p, ε p * ε p = 1) (z : EuclideanSpace ℝ ι) (p : ι) :
    signE ε hε z p = ε p * z p := rfl

/-- Coordinate permutation, an isometry. -/
noncomputable def permE (σ : ι ≃ ι) : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι where
  toFun z := WithLp.toLp 2 (fun p => z (σ p))
  invFun z := WithLp.toLp 2 (fun p => z (σ.symm p))
  map_add' x y := by ext p; simp
  map_smul' c x := by ext p; simp
  left_inv z := by ext p; simp
  right_inv z := by ext p; simp
  norm_map' z := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp only [PiLp.toLp_apply, LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk]
    exact Equiv.sum_comp σ (fun p => ‖z p‖ ^ 2)

lemma permE_apply (σ : ι ≃ ι) (z : EuclideanSpace ℝ ι) (p : ι) : permE σ z p = z (σ p) := rfl

lemma int_iso {β : Type} [NormedAddCommGroup β] [NormedSpace ℝ β]
    (f : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) (g : EuclideanSpace ℝ ι → β) :
    ∫ z, g (f z) ∂(stdGaussian (EuclideanSpace ℝ ι)) = ∫ z, g z ∂(stdGaussian (EuclideanSpace ℝ ι)) := by
  have h : MeasurePreserving f (stdGaussian (EuclideanSpace ℝ ι)) (stdGaussian (EuclideanSpace ℝ ι)) :=
    ⟨f.continuous.measurable, stdGaussian_map f⟩
  exact h.integral_comp f.toHomeomorph.measurableEmbedding g

lemma int_odd (f : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) (g : EuclideanSpace ℝ ι → ℝ)
    (hg : ∀ z, g (f z) = - g z) : ∫ z, g z ∂(stdGaussian (EuclideanSpace ℝ ι)) = 0 := by
  have h := int_iso f g
  simp_rw [hg, integral_neg] at h
  linarith

/-- Flip of one coordinate. -/
noncomputable def flip1 (a : ι) : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι :=
  signE (fun p => if p = a then -1 else 1) (fun p => by split_ifs <;> norm_num)

lemma flip1_apply (a : ι) (z : EuclideanSpace ℝ ι) (p : ι) :
    flip1 a z p = if p = a then - z p else z p := by
  simp only [flip1, signE_apply]; split_ifs <;> ring

lemma mono_odd (a b c d : ι) (hb : b ≠ a) (hc : c ≠ a) (hd : d ≠ a) :
    ∫ z : EuclideanSpace ℝ ι, z a * z b * z c * z d ∂(stdGaussian (EuclideanSpace ℝ ι)) = 0 :=
  int_odd (flip1 a) _ fun z => by simp only [flip1_apply, if_neg hb, if_neg hc, if_neg hd, ↓reduceIte]; ring

lemma mom2 (a : ι) : ∫ z : EuclideanSpace ℝ ι, z a ^ 2 ∂(stdGaussian (EuclideanSpace ℝ ι)) = 1 := by
  rw [int_coord a (fun t => t ^ 2) (by fun_prop), gauss_mom2]; simp

lemma mom4 (a : ι) : ∫ z : EuclideanSpace ℝ ι, z a ^ 4 ∂(stdGaussian (EuclideanSpace ℝ ι)) = 3 := by
  rw [int_coord a (fun t => t ^ 4) (by fun_prop), gauss_mom4]; simp

lemma mom22 (a b : ι) (hab : a ≠ b) :
    ∫ z : EuclideanSpace ℝ ι, z a ^ 2 * z b ^ 2 ∂(stdGaussian (EuclideanSpace ℝ ι)) = 1 := by
  set f : ι → ℝ → ℝ := fun p => if p = a ∨ p = b then (fun t => t ^ 2) else (fun _ => 1) with hf
  have hprod : ∀ z : EuclideanSpace ℝ ι, z a ^ 2 * z b ^ 2 = ∏ p, f p (z p) := by
    intro z
    rw [Fintype.prod_eq_mul a b hab (fun x hx => by simp [hf, hx.1, hx.2])]
    simp [hf]
  simp_rw [hprod]
  rw [← map_pi_eq_stdGaussian, integral_map (by fun_prop)
    (by refine Measurable.aestronglyMeasurable ?_
        exact Finset.measurable_prod _ fun p _ => by
          by_cases h : p = a ∨ p = b
          · simp only [hf, if_pos h]; fun_prop
          · simp only [hf, if_neg h]; fun_prop)]
  simp only [PiLp.toLp_apply]
  rw [integral_fintype_prod_eq_prod, Fintype.prod_eq_mul a b hab (fun x hx => by simp [hf, hx.1, hx.2])]
  simp [hf, gauss_mom2]

end E2C4

namespace E2Plan

noncomputable def grX {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m ⊕ Fin m) (Fin m) ℂ :=
  Matrix.fromRows (1 : Matrix (Fin m) (Fin m) ℂ) A

noncomputable def gr {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℂ :=
  grX A * (Matrix.conjTranspose (grX A) * grX A)⁻¹ * Matrix.conjTranspose (grX A)

lemma grX_gram {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) :
    Matrix.conjTranspose (grX A) * grX A = 1 + Matrix.conjTranspose A * A := by
  simp [grX, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromRows]

lemma gram_posDef {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) :
    (1 + Matrix.conjTranspose A * A).PosDef :=
  Matrix.PosDef.one.add_posSemidef (Matrix.posSemidef_conjTranspose_mul_self A)

lemma gram_isUnit {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) :
    IsUnit (Matrix.conjTranspose (grX A) * grX A).det := by
  rw [grX_gram]; exact (gram_posDef A).isUnit.map Matrix.detMonoidHom

lemma gr_isHermitian {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : (gr A).IsHermitian := by
  have hH : ((Matrix.conjTranspose (grX A) * grX A)⁻¹).IsHermitian :=
    (Matrix.isHermitian_conjTranspose_mul_self (grX A)).inv
  unfold gr
  rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hH.eq, Matrix.mul_assoc]

lemma gr_idem {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : gr A * gr A = gr A := by
  have h := Matrix.nonsing_inv_mul _ (gram_isUnit A)
  unfold gr
  set X := grX A
  set M := (Matrix.conjTranspose X * X)⁻¹
  calc X * M * Matrix.conjTranspose X * (X * M * Matrix.conjTranspose X)
      = X * (M * (Matrix.conjTranspose X * X)) * M * Matrix.conjTranspose X := by
        simp only [Matrix.mul_assoc]
    _ = X * M * Matrix.conjTranspose X := by rw [h, Matrix.mul_one]

lemma gr_trace {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : (gr A).trace = (m : ℂ) := by
  have h := Matrix.mul_nonsing_inv _ (gram_isUnit A)
  unfold gr
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, h, Matrix.trace_one]
  simp

theorem C2 (m : ℕ) (A : Matrix (Fin m) (Fin m) ℂ) :
    (gr A).IsHermitian ∧ gr A * gr A = gr A ∧ (gr A).trace = (m : ℂ) :=
  ⟨gr_isHermitian A, gr_idem A, gr_trace A⟩

/-- Squared Frobenius norm. -/
noncomputable def fr2 {p q : Type} [Fintype p] [Fintype q] (M : Matrix p q ℂ) : ℝ :=
  (Matrix.conjTranspose M * M).trace.re

lemma psd_trace_re_nonneg {p : Type} [Fintype p] {M : Matrix p p ℂ} (h : M.PosSemidef) :
    0 ≤ M.trace.re :=
  (Complex.le_def.1 h.trace_nonneg).1

lemma fr2_nonneg {p q : Type} [Fintype p] [Fintype q] (M : Matrix p q ℂ) : 0 ≤ fr2 M :=
  psd_trace_re_nonneg (Matrix.posSemidef_conjTranspose_mul_self M)

lemma fr2_proj_mul {p q : Type} [Fintype p] [Fintype q] [DecidableEq p]
    (Q : Matrix p p ℂ) (hQh : Q.IsHermitian) (hQ : Q * Q = Q) (M : Matrix p q ℂ) :
    fr2 (Q * M) ≤ fr2 M := by
  have h1 : (1 - Q) * (1 - Q) = 1 - Q := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hQ]; abel
  have hR : (1 - Q).IsHermitian := by
    simp [Matrix.IsHermitian, Matrix.conjTranspose_sub, hQh.eq]
  have key : Matrix.conjTranspose M * M - Matrix.conjTranspose (Q * M) * (Q * M)
      = Matrix.conjTranspose ((1 - Q) * M) * ((1 - Q) * M) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hQh.eq, hR.eq]
    have e1 : Matrix.conjTranspose M * Q * (Q * M) = Matrix.conjTranspose M * Q * M := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q Q M, hQ, Matrix.mul_assoc]
    have e2 : Matrix.conjTranspose M * (1 - Q) * ((1 - Q) * M)
        = Matrix.conjTranspose M * (1 - Q) * M := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (1 - Q) (1 - Q) M, h1, Matrix.mul_assoc]
    rw [e1, e2, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc]
  have hnn := psd_trace_re_nonneg (Matrix.posSemidef_conjTranspose_mul_self ((1 - Q) * M))
  rw [← key, Matrix.trace_sub, Complex.sub_re] at hnn
  unfold fr2; linarith

lemma fr2_mul_contr {p q r : Type} [Fintype p] [Fintype q] [Fintype r] [DecidableEq q]
    (M : Matrix p q ℂ) (N : Matrix q r ℂ) (h : (1 - N * Matrix.conjTranspose N).PosSemidef) :
    fr2 (M * N) ≤ fr2 M := by
  have hnn := psd_trace_re_nonneg (h.mul_mul_conjTranspose_same M)
  have e : M * (1 - N * Matrix.conjTranspose N) * Matrix.conjTranspose M
      = M * Matrix.conjTranspose M - (M * N) * Matrix.conjTranspose (M * N) := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    simp only [Matrix.mul_assoc]
  rw [e, Matrix.trace_sub, Complex.sub_re] at hnn
  unfold fr2
  rw [Matrix.trace_mul_comm (Matrix.conjTranspose (M * N)), Matrix.trace_mul_comm (Matrix.conjTranspose M)]
  linarith

/-- `1 - (1+S)⁻¹` is PSD for PSD `S`. -/
lemma one_sub_inv_psd {q : Type} [Fintype q] [DecidableEq q] (S : Matrix q q ℂ)
    (hS : S.PosSemidef) : (1 - (1 + S)⁻¹).PosSemidef := by
  have hG : (1 + S).PosDef := Matrix.PosDef.one.add_posSemidef hS
  have hu : IsUnit (1 + S).det := hG.isUnit.map Matrix.detMonoidHom
  set R := (1 + S)⁻¹ with hRdef
  have hRh : R.IsHermitian := hG.isHermitian.inv
  have hSh : S.IsHermitian := hS.isHermitian
  have hRG : R * (1 + S) = 1 := Matrix.nonsing_inv_mul _ hu
  have hGR : (1 + S) * R = 1 := Matrix.mul_nonsing_inv _ hu
  have hcomm : S * R = R * S := by
    have a : R + R * S = 1 := by rw [← hRG, Matrix.mul_add, Matrix.mul_one]
    have b : R + S * R = 1 := by rw [← hGR, Matrix.add_mul, Matrix.one_mul]
    have := a.trans b.symm
    exact (add_left_cancel this).symm
  have hdecomp : 1 - R = Matrix.conjTranspose R * S * R
      + Matrix.conjTranspose (S * R) * (S * R) := by
    rw [Matrix.conjTranspose_mul, hRh.eq, hSh.eq]
    have a : R + R * S = 1 := by rw [← hRG, Matrix.mul_add, Matrix.mul_one]
    have hRS : 1 - R = R * S := by rw [← a]; abel
    rw [hRS]
    calc R * S = R * S * ((1 + S) * R) := by rw [hGR, Matrix.mul_one]
      _ = R * S * R + R * S * (S * R) := by
        rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add]
      _ = R * S * R + R * S * (S * R) := rfl
  rw [hdecomp]
  exact (hS.conjTranspose_mul_mul_same R).add (Matrix.posSemidef_conjTranspose_mul_self _)


noncomputable def grPinv {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : Matrix (Fin m) (Fin m ⊕ Fin m) ℂ :=
  (Matrix.conjTranspose (grX A) * grX A)⁻¹ * Matrix.conjTranspose (grX A)

lemma gr_eq {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : gr A = grX A * grPinv A := by
  unfold gr grPinv; rw [Matrix.mul_assoc]

lemma gr_mul_X {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) : gr A * grX A = grX A := by
  unfold gr
  rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (gram_isUnit A), Matrix.mul_one]

lemma pinv_contr {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) :
    (1 - grPinv A * Matrix.conjTranspose (grPinv A)).PosSemidef := by
  have hH : ((Matrix.conjTranspose (grX A) * grX A)⁻¹).IsHermitian :=
    (Matrix.isHermitian_conjTranspose_mul_self (grX A)).inv
  have e : grPinv A * Matrix.conjTranspose (grPinv A) = (1 + Matrix.conjTranspose A * A)⁻¹ := by
    unfold grPinv
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hH.eq]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (Matrix.conjTranspose (grX A)),
      Matrix.mul_nonsing_inv _ (gram_isUnit A), Matrix.mul_one, grX_gram]
  rw [e]
  exact one_sub_inv_psd _ (Matrix.posSemidef_conjTranspose_mul_self A)

lemma fr2_grX_sub {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) :
    fr2 (grX A - grX B) = fr2 (A - B) := by
  have h : grX A - grX B = Matrix.fromRows (0 : Matrix (Fin m) (Fin m) ℂ) (A - B) := by
    ext i j; rcases i with i | i <;> simp [grX]
  unfold fr2
  rw [h, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromRows]
  simp

/-- One cross term: `‖(1 - P_B) P_A‖² ≤ ‖A - B‖²`. -/
lemma fr2_cross {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) :
    fr2 ((1 - gr B) * gr A) ≤ fr2 (A - B) := by
  have hQh : (1 - gr B).IsHermitian := by
    simp [Matrix.IsHermitian, Matrix.conjTranspose_sub, (gr_isHermitian B).eq]
  have hQ : (1 - gr B) * (1 - gr B) = 1 - gr B := by
    rw [sub_mul, one_mul, mul_sub, mul_one, gr_idem]; abel
  have hk : (1 - gr B) * grX B = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, gr_mul_X, sub_self]
  have e : (1 - gr B) * gr A = (1 - gr B) * (grX A - grX B) * grPinv A := by
    calc (1 - gr B) * gr A = (1 - gr B) * (grX A * grPinv A) := by rw [← gr_eq]
      _ = ((1 - gr B) * grX A) * grPinv A := by rw [Matrix.mul_assoc]
      _ = ((1 - gr B) * (grX A - grX B)) * grPinv A := by rw [Matrix.mul_sub, hk, sub_zero]
  rw [e]
  calc fr2 ((1 - gr B) * (grX A - grX B) * grPinv A)
      ≤ fr2 ((1 - gr B) * (grX A - grX B)) := fr2_mul_contr _ _ (pinv_contr A)
    _ ≤ fr2 (grX A - grX B) := fr2_proj_mul _ hQh hQ _
    _ = fr2 (A - B) := fr2_grX_sub A B

/-- `‖P_A - P_B‖² ≤ 2 ‖A - B‖²` (squared Frobenius). -/
lemma fr2_gr_sub {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) :
    fr2 (gr A - gr B) ≤ 2 * fr2 (A - B) := by
  set P := gr A
  set Q := gr B
  have hP : P.IsHermitian := gr_isHermitian A
  have hQh : Q.IsHermitian := gr_isHermitian B
  have hQ : Q * Q = Q := gr_idem B
  set a := (1 - Q) * P
  set b := Q * (1 - P)
  have hsplit : P - Q = a - b := by
    simp only [a, b, sub_mul, one_mul, mul_sub, mul_one]; abel
  have hab : Matrix.conjTranspose a * b = 0 := by
    simp only [a, b, Matrix.conjTranspose_mul, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_one, hP.eq, hQh.eq]
    have : (1 - Q) * Q = 0 := by rw [sub_mul, one_mul, hQ, sub_self]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (1 - Q) Q, this, Matrix.zero_mul, Matrix.mul_zero]
  have hba : Matrix.conjTranspose b * a = 0 := by
    have := congrArg Matrix.conjTranspose hab
    simpa [Matrix.conjTranspose_mul] using this
  have hfr : fr2 (a - b) = fr2 a + fr2 b := by
    unfold fr2
    rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hab, hba]
    simp [Matrix.trace_add]
  have hb : fr2 b = fr2 ((1 - P) * Q) := by
    unfold fr2
    have hbT : Matrix.conjTranspose b = (1 - P) * Q := by
      simp [b, Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, hP.eq, hQh.eq]
    rw [Matrix.trace_mul_comm, ← hbT, Matrix.conjTranspose_conjTranspose]
  have h1 : fr2 a ≤ fr2 (A - B) := fr2_cross A B
  have h2 : fr2 ((1 - P) * Q) ≤ fr2 (B - A) := fr2_cross B A
  have hsym : fr2 (B - A) = fr2 (A - B) := by
    unfold fr2; rw [← neg_sub, Matrix.conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, neg_neg]
  rw [hsplit, hfr, hb]
  linarith

/-- `re Tr(P_A P_B) = m - ‖P_A - P_B‖²/2`. -/
lemma trace_gr_mul {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) :
    (gr A * gr B).trace.re = (m : ℝ) - fr2 (gr A - gr B) / 2 := by
  have hP := gr_isHermitian A
  have hQ := gr_isHermitian B
  have e : fr2 (gr A - gr B) = 2 * (m : ℝ) - 2 * (gr A * gr B).trace.re := by
    unfold fr2
    rw [Matrix.conjTranspose_sub, hP.eq, hQ.eq, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub,
      gr_idem, gr_idem, Matrix.trace_sub, Matrix.trace_sub, Matrix.trace_sub,
      Matrix.trace_mul_comm (gr B) (gr A), gr_trace, gr_trace]
    simp only [Complex.sub_re, Complex.natCast_re]
    ring
  rw [e]; ring


theorem C5 (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Bad : Set (Ω × Ω)) (hB : MeasurableSet Bad) (n : ℕ) (q : ℝ)
    (hq : (μ.prod μ).real Bad ≤ q) (hn : (n : ℝ) ^ 2 * q < 1) :
    ∃ x : Fin n → Ω, ∀ i j, i ≠ j → (x i, x j) ∉ Bad := by
  classical
  by_contra hne
  push Not at hne
  set ν : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ) with hν
  have hind : iIndepFun (fun (i : Fin n) (x : Fin n → Ω) => x i) ν :=
    iIndepFun_pi (X := fun _ (y : Ω) => y) (fun _ => aemeasurable_id)
  have hpair : ∀ p : Fin n × Fin n, p.1 ≠ p.2 →
      ν ((fun x : Fin n → Ω => (x p.1, x p.2)) ⁻¹' Bad) = (μ.prod μ) Bad := by
    intro p hp
    have h2 : IndepFun (fun x : Fin n → Ω => x p.1) (fun x => x p.2) ν := hind.indepFun hp
    have hm1 : AEMeasurable (fun x : Fin n → Ω => x p.1) ν := (measurable_pi_apply _).aemeasurable
    have hm2 : AEMeasurable (fun x : Fin n → Ω => x p.2) ν := (measurable_pi_apply _).aemeasurable
    rw [← Measure.map_apply (by fun_prop) hB,
      (indepFun_iff_map_prod_eq_prod_map_map hm1 hm2).1 h2,
      (measurePreserving_eval (fun _ : Fin n => μ) p.1).map_eq,
      (measurePreserving_eval (fun _ : Fin n => μ) p.2).map_eq]
  have hsub : (Set.univ : Set (Fin n → Ω)) ⊆
      ⋃ p : Fin n × Fin n, ⋃ (_ : p.1 ≠ p.2), (fun x : Fin n → Ω => (x p.1, x p.2)) ⁻¹' Bad := by
    intro x _
    obtain ⟨i, j, hij, hx⟩ := hne x
    simp only [Set.mem_iUnion, Set.mem_preimage]
    exact ⟨(i, j), hij, hx⟩
  have hle : (1 : ENNReal) ≤ (n : ENNReal) ^ 2 * (μ.prod μ) Bad := by
    calc (1 : ENNReal) = ν Set.univ := by simp [hν]
      _ ≤ ν (⋃ p : Fin n × Fin n, ⋃ (_ : p.1 ≠ p.2),
            (fun x : Fin n → Ω => (x p.1, x p.2)) ⁻¹' Bad) := measure_mono hsub
      _ ≤ ∑ p : Fin n × Fin n, ν (⋃ (_ : p.1 ≠ p.2),
            (fun x : Fin n → Ω => (x p.1, x p.2)) ⁻¹' Bad) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _p : Fin n × Fin n, (μ.prod μ) Bad := by
            refine Finset.sum_le_sum fun p _ => ?_
            by_cases hp : p.1 = p.2
            · simp [hp]
            · exact (measure_mono (Set.iUnion_subset fun _ => subset_rfl)).trans (hpair p hp).le
      _ = (n : ENNReal) ^ 2 * (μ.prod μ) Bad := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, sq]
  have hfin : (μ.prod μ) Bad ≠ ⊤ := measure_ne_top _ _
  have hreal : (1 : ℝ) ≤ (n : ℝ) ^ 2 * (μ.prod μ).real Bad := by
    have := (ENNReal.toReal_le_toReal (by simp) (ENNReal.mul_ne_top (by simp) hfin)).2 hle
    simpa [measureReal_def, ENNReal.toReal_mul] using this
  have h0 : 0 ≤ (n : ℝ) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hq h0]


/-- Real Gaussian matrix scaled by `τ/√m`, cast to `ℂ`. -/
noncomputable def matA {m : ℕ} (τ : ℝ) (z : EuclideanSpace ℝ (Fin m × Fin m)) :
    Matrix (Fin m) (Fin m) ℂ :=
  fun i j => (((τ / Real.sqrt m) * z (i, j) : ℝ) : ℂ)

/-- The pair statistic `Tr(P_A P_B)`. -/
noncomputable def F2 {m : ℕ} (τ : ℝ)
    (p : EuclideanSpace ℝ (Fin m × Fin m) × EuclideanSpace ℝ (Fin m × Fin m)) : ℝ :=
  (gr (matA τ p.1) * gr (matA τ p.2)).trace.re

lemma fr2_eq_sum {p q : Type} [Fintype p] [Fintype q] (M : Matrix p q ℂ) :
    fr2 M = ∑ i, ∑ j, ‖M i j‖ ^ 2 := by
  unfold fr2
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  simp [Complex.mul_re]

open scoped Matrix.Norms.Frobenius in
lemma fr2_eq_norm_sq {p q : Type} [Fintype p] [Fintype q] (M : Matrix p q ℂ) :
    fr2 M = ‖M‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def, fr2_eq_sum, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  norm_num

open scoped Matrix.Norms.Frobenius in
lemma norm_gr_sub {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) :
    ‖gr A - gr B‖ ≤ Real.sqrt 2 * ‖A - B‖ := by
  have h := fr2_gr_sub A B
  rw [fr2_eq_norm_sq, fr2_eq_norm_sq] at h
  have := (le_abs_self _).trans (Real.abs_le_sqrt h)
  rwa [Real.sqrt_mul (by norm_num), Real.sqrt_sq (norm_nonneg _)] at this

lemma trace_gr_mul_nonneg {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) :
    0 ≤ (gr A * gr B).trace.re := by
  have hP := gr_isHermitian A
  have hQ := gr_isHermitian B
  have e : (gr A * gr B).trace
      = (Matrix.conjTranspose (gr B * gr A) * (gr B * gr A)).trace := by
    rw [Matrix.conjTranspose_mul, hP.eq, hQ.eq]
    calc (gr A * gr B).trace = (gr A * (gr A * (gr B * gr B))).trace := by
          rw [gr_idem, ← Matrix.mul_assoc, gr_idem]
      _ = (gr A * (gr B * gr B) * gr A).trace := by
          rw [Matrix.trace_mul_comm (gr A) (gr A * (gr B * gr B)), Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [e]; exact fr2_nonneg _

open scoped Matrix.Norms.Frobenius in
lemma norm_gr_sub_le {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℂ) :
    ‖gr A - gr B‖ ≤ Real.sqrt (2 * m) := by
  have h1 := trace_gr_mul A B
  have h2 := trace_gr_mul_nonneg A B
  have h3 : ‖gr A - gr B‖ ^ 2 ≤ 2 * m := by rw [← fr2_eq_norm_sq]; linarith
  exact (le_abs_self _).trans (Real.abs_le_sqrt h3)

lemma matA_sub {m : ℕ} (τ : ℝ) (z z' : EuclideanSpace ℝ (Fin m × Fin m)) :
    matA τ z - matA τ z' = matA τ (z - z') := by
  ext i j; simp [matA, mul_sub]

open scoped Matrix.Norms.Frobenius in
lemma norm_matA {m : ℕ} (τ : ℝ) (x : EuclideanSpace ℝ (Fin m × Fin m)) :
    ‖matA τ x‖ = |τ / Real.sqrt m| * ‖x‖ := by
  have h : ‖matA τ x‖ ^ 2 = (|τ / Real.sqrt m| * ‖x‖) ^ 2 := by
    rw [← fr2_eq_norm_sq, mul_pow, sq_abs, EuclideanSpace.norm_sq_eq, fr2_eq_sum,
      Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [matA, Complex.norm_real, Real.norm_eq_abs, abs_mul, mul_pow, sq_abs]
  exact (pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

lemma real_sq_core (a b d s : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : a ≤ s) (hb' : b ≤ s)
    (hd : |a - b| ≤ d) : |a ^ 2 - b ^ 2| / 2 ≤ d * s := by
  rw [show a ^ 2 - b ^ 2 = (a - b) * (a + b) by ring, abs_mul, abs_of_nonneg (show 0 ≤ a + b by positivity)]
  have hd0 : 0 ≤ d := (abs_nonneg _).trans hd
  have : |a - b| * (a + b) ≤ d * (2 * s) :=
    mul_le_mul hd (by linarith) (by positivity) hd0
  linarith

open scoped Matrix.Norms.Frobenius in
lemma lip_core {n : Type} [Fintype n] (P Q P' Q' : Matrix n n ℂ) (s c dz dw : ℝ)
    (hb : ‖P - Q‖ ≤ s) (hb' : ‖P' - Q'‖ ≤ s) (h1 : ‖P - P'‖ ≤ c * dz) (h2 : ‖Q - Q'‖ ≤ c * dw) :
    |‖P - Q‖ ^ 2 - ‖P' - Q'‖ ^ 2| / 2 ≤ c * (dz + dw) * s := by
  have hD : ‖(P - Q) - (P' - Q')‖ ≤ ‖P - P'‖ + ‖Q - Q'‖ := by
    have e : (P - Q) - (P' - Q') = (P - P') - (Q - Q') := by abel
    rw [e]; exact norm_sub_le _ _
  have hdiff : |‖P - Q‖ - ‖P' - Q'‖| ≤ ‖(P - Q) - (P' - Q')‖ := abs_norm_sub_norm_le _ _
  have := real_sq_core ‖P - Q‖ ‖P' - Q'‖ (c * dz + c * dw) s (norm_nonneg _) (norm_nonneg _) hb hb'
    (by linarith)
  linarith

open scoped Matrix.Norms.Frobenius in
lemma F2_lip {m : ℕ} (hm : 0 < m) (τ : ℝ) (hτ : 0 < τ)
    (p p' : EuclideanSpace ℝ (Fin m × Fin m) × EuclideanSpace ℝ (Fin m × Fin m)) :
    |F2 τ p - F2 τ p'| ≤ 2 * τ * (‖p.1 - p'.1‖ + ‖p.2 - p'.2‖) := by
  have hc : 0 < τ / Real.sqrt m := by positivity
  have h1 := norm_gr_sub (matA τ p.1) (matA τ p'.1)
  rw [matA_sub, norm_matA, abs_of_pos hc, ← mul_assoc] at h1
  have h2 := norm_gr_sub (matA τ p.2) (matA τ p'.2)
  rw [matA_sub, norm_matA, abs_of_pos hc, ← mul_assoc] at h2
  have core := lip_core (gr (matA τ p.1)) (gr (matA τ p.2)) (gr (matA τ p'.1)) (gr (matA τ p'.2))
    (Real.sqrt (2 * m)) (Real.sqrt 2 * (τ / Real.sqrt m)) ‖p.1 - p'.1‖ ‖p.2 - p'.2‖
    (norm_gr_sub_le _ _) (norm_gr_sub_le _ _) h1 h2
  have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hm' : Real.sqrt (m : ℝ) ≠ 0 := by positivity
  have hs : Real.sqrt 2 * (τ / Real.sqrt m) * Real.sqrt (2 * m) = 2 * τ := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have e : Real.sqrt 2 * (τ / Real.sqrt m) * (Real.sqrt 2 * Real.sqrt m)
        = (Real.sqrt 2 * Real.sqrt 2) * τ * (Real.sqrt m / Real.sqrt m) := by ring
    rw [e, hsq2, div_self hm']; ring
  have hF : F2 τ p - F2 τ p' = -(‖gr (matA τ p.1) - gr (matA τ p.2)‖ ^ 2
      - ‖gr (matA τ p'.1) - gr (matA τ p'.2)‖ ^ 2) / 2 := by
    rw [F2, F2, trace_gr_mul, trace_gr_mul, fr2_eq_norm_sq, fr2_eq_norm_sq]; ring
  rw [hF, abs_div, abs_neg, abs_two]
  calc _ ≤ _ := core
    _ = (Real.sqrt 2 * (τ / Real.sqrt m) * Real.sqrt (2 * m)) * (‖p.1 - p'.1‖ + ‖p.2 - p'.2‖) := by
        ring
    _ = _ := by rw [hs]

lemma F2_lipschitz {m : ℕ} (hm : 0 < m) (τ : ℝ) (hτ : 0 < τ) :
    LipschitzWith (Real.toNNReal (4 * τ)) (F2 (m := m) τ) := by
  refine LipschitzWith.of_dist_le_mul fun p p' => ?_
  rw [Real.coe_toNNReal _ (by positivity), Real.dist_eq]
  have h := F2_lip hm τ hτ p p'
  have d1 : ‖p.1 - p'.1‖ ≤ dist p p' := by
    rw [← dist_eq_norm, Prod.dist_eq]; exact le_max_left _ _
  have d2 : ‖p.2 - p'.2‖ ≤ dist p p' := by
    rw [← dist_eq_norm, Prod.dist_eq]; exact le_max_right _ _
  nlinarith

lemma gr_blocks {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) :
    gr A = Matrix.fromBlocks ((1 + Aᴴ * A)⁻¹) ((1 + Aᴴ * A)⁻¹ * Aᴴ)
      (A * (1 + Aᴴ * A)⁻¹) (A * (1 + Aᴴ * A)⁻¹ * Aᴴ) := by
  rw [gr, grX_gram]
  unfold grX
  rw [Matrix.fromRows_mul, Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.fromRows_mul_fromCols]
  simp

open scoped Matrix.Norms.Frobenius in
lemma F2_differentiable {m : ℕ} (τ : ℝ) : Differentiable ℝ (F2 (m := m) τ) := by
  classical
  have : CompleteSpace (Matrix (Fin m) (Fin m) ℂ) := FiniteDimensional.complete ℝ _
  let LA : EuclideanSpace ℝ (Fin m × Fin m) →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ :=
    { toFun := matA τ
      map_add' := fun x y => by ext i j; simp [matA, mul_add]
      map_smul' := fun c x => by ext i j; simp [matA]; ring }
  let LH : Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ :=
    { toFun := Matrix.conjTranspose
      map_add' := Matrix.conjTranspose_add
      map_smul' := fun c A => by ext i j; simp }
  let LB : (Matrix (Fin m) (Fin m) ℂ × Matrix (Fin m) (Fin m) ℂ) ×
      (Matrix (Fin m) (Fin m) ℂ × Matrix (Fin m) (Fin m) ℂ) →ₗ[ℝ]
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℂ :=
    { toFun := fun x => Matrix.fromBlocks x.1.1 x.1.2 x.2.1 x.2.2
      map_add' := fun x y => (Matrix.fromBlocks_add _ _ _ _ _ _ _ _).symm
      map_smul' := fun c x => (Matrix.fromBlocks_smul _ _ _ _ _).symm }
  have hG : ∀ f : EuclideanSpace ℝ (Fin m × Fin m) × EuclideanSpace ℝ (Fin m × Fin m) →
      EuclideanSpace ℝ (Fin m × Fin m), Differentiable ℝ f →
      Differentiable ℝ (fun p => gr (matA τ (f p))) := by
    intro f hf
    have hA : Differentiable ℝ (fun p => matA τ (f p)) :=
      LA.toContinuousLinearMap.differentiable.comp hf
    have hAH : Differentiable ℝ (fun p => (matA τ (f p))ᴴ) :=
      LH.toContinuousLinearMap.differentiable.comp hA
    have hR : Differentiable ℝ (fun p => (1 + (matA τ (f p))ᴴ * matA τ (f p))⁻¹) := by
      intro p
      simp_rw [Matrix.nonsing_inv_eq_ringInverse]
      exact (differentiableAt_inverse (gram_posDef _).isUnit).comp p
        ((differentiable_const _).add (hAH.mul hA) p)
    have hblk : (fun p => gr (matA τ (f p))) = fun p => LB
        (((1 + (matA τ (f p))ᴴ * matA τ (f p))⁻¹,
          (1 + (matA τ (f p))ᴴ * matA τ (f p))⁻¹ * (matA τ (f p))ᴴ),
         (matA τ (f p) * (1 + (matA τ (f p))ᴴ * matA τ (f p))⁻¹,
          matA τ (f p) * (1 + (matA τ (f p))ᴴ * matA τ (f p))⁻¹ * (matA τ (f p))ᴴ)) := by
      funext p; rw [gr_blocks]; rfl
    rw [hblk]
    exact LB.toContinuousLinearMap.differentiable.comp
      ((hR.prodMk (hR.mul hAH)).prodMk ((hA.mul hR).prodMk ((hA.mul hR).mul hAH)))
  have h1 := hG Prod.fst differentiable_fst
  have h2 := hG Prod.snd differentiable_snd
  have hT := (Matrix.traceLinearMap (Fin m ⊕ Fin m) ℝ ℂ).toContinuousLinearMap.differentiable
  exact Complex.reCLM.differentiable.comp (hT.comp (h1.mul h2))

/-- C1 (PROVED): Gaussian concentration for differentiable Lipschitz functions of an i.i.d.
Gaussian pair (Maurey–Pisier). -/
def C1_gauss_conc : Prop :=
  ∀ (ι : Type) [Fintype ι]
    (f : EuclideanSpace ℝ ι × EuclideanSpace ℝ ι → ℝ) (L : NNReal),
    Differentiable ℝ f → LipschitzWith L f → (∃ M : ℝ, ∀ p, |f p| ≤ M) → ∀ t : ℝ, 0 < t →
      ((stdGaussian (EuclideanSpace ℝ ι)).prod (stdGaussian (EuclideanSpace ℝ ι))).real
          {p | t ≤ |f p - ∫ q, f q ∂((stdGaussian (EuclideanSpace ℝ ι)).prod
              (stdGaussian (EuclideanSpace ℝ ι)))|}
        ≤ 2 * Real.exp (-(2 * t ^ 2) / (Real.pi ^ 2 * (L : ℝ) ^ 2))

theorem C1 : C1_gauss_conc := E2C1.C1

/-- C3 (PROVED): the statistic is differentiable and Lipschitz, uniformly in `m`. -/
def C3_F_lipschitz : Prop :=
  ∀ τ : ℝ, 0 < τ → ∃ L : NNReal, ∀ m : ℕ, 0 < m →
    Differentiable ℝ (F2 (m := m) τ) ∧ LipschitzWith L (F2 (m := m) τ)

theorem C3 : C3_F_lipschitz := fun τ hτ =>
  ⟨Real.toNNReal (4 * τ), fun _ hm => ⟨F2_differentiable τ, F2_lipschitz hm τ hτ⟩⟩

/-- C4 (OPEN): the mean of the statistic lies in `[m/2, 13m/24]` for a suitable `τ`. -/
def C4_mean : Prop :=
  ∃ τ : ℝ, 0 < τ ∧ ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
    (m : ℝ) / 2 ≤ ∫ p, F2 (m := m) τ p ∂((stdGaussian (EuclideanSpace ℝ (Fin m × Fin m))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin m × Fin m)))) ∧
    ∫ p, F2 (m := m) τ p ∂((stdGaussian (EuclideanSpace ℝ (Fin m × Fin m))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin m × Fin m)))) ≤ 13 * (m : ℝ) / 24


-- ==== C4 part B: diagonal bounds for (1 + AᴴA)⁻¹ ====

lemma re_nonneg_of_psd {n : Type} [Fintype n] {M : Matrix n n ℂ} (h : M.PosSemidef) (i : n) :
    0 ≤ (M i i).re := by
  have := h.diag_nonneg (i := i)
  exact (Complex.le_def.1 this).1

lemma inv_diag_bounds {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (i : Fin m) (y : ℝ) :
    (1 + y) - (((Aᴴ * A) i i).re - y) ≤ (1 + y) ^ 2 * ((1 + Aᴴ * A)⁻¹ i i).re ∧
    (1 + y) ^ 2 * ((1 + Aᴴ * A)⁻¹ i i).re
      ≤ ((Aᴴ * A * (Aᴴ * A)) i i).re - (1 + 2 * y) * ((Aᴴ * A) i i).re + (1 + y) ^ 2 := by
  set W := Aᴴ * A with hW
  set G := 1 + W with hG
  set K := W - (y : ℂ) • (1 : Matrix (Fin m) (Fin m) ℂ) with hK
  have hpd : G.PosDef := gram_posDef A
  have hu : IsUnit G.det := hpd.isUnit.map Matrix.detMonoidHom
  have h1 : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul _ hu
  have h2 : G * G⁻¹ = 1 := Matrix.mul_nonsing_inv _ hu
  have hGK : G = K + ((1 + y : ℝ) : ℂ) • 1 := by
    rw [hG, hK]; push_cast; rw [add_smul, one_smul]; abel
  have hKG : K = G - ((1 + y : ℝ) : ℂ) • 1 := by rw [hGK]; abel
  have hK1 : G⁻¹ * K = 1 - ((1 + y : ℝ) : ℂ) • G⁻¹ := by
    rw [hKG, Matrix.mul_sub, h1, Matrix.mul_smul, Matrix.mul_one]
  have hK2 : K * G⁻¹ = 1 - ((1 + y : ℝ) : ℂ) • G⁻¹ := by
    rw [hKG, Matrix.sub_mul, h2, Matrix.smul_mul, Matrix.one_mul]
  have hKGK : K * G⁻¹ * K = K - ((1 + y : ℝ) : ℂ) • 1 + (((1 + y) ^ 2 : ℝ) : ℂ) • G⁻¹ := by
    rw [hK2, Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul, hK1, smul_sub, smul_smul,
      ← Complex.ofReal_mul, ← sq]
    abel
  have hKK : K * K = W * W - ((2 * y : ℝ) : ℂ) • W + ((y ^ 2 : ℝ) : ℂ) • 1 := by
    rw [hK]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one, smul_smul]
    push_cast
    module
  have hWh : Wᴴ = W := by rw [hW, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hKh : Kᴴ = K := by
    rw [hK, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_one, hWh,
      Complex.star_def, Complex.conj_ofReal]
  have p1 : (K * G⁻¹ * K).PosSemidef := by
    have := hpd.inv.posSemidef.conjTranspose_mul_mul_same K
    rwa [hKh] at this
  have p2 : (K * (1 - G⁻¹) * K).PosSemidef := by
    have := (one_sub_inv_psd W (Matrix.posSemidef_conjTranspose_mul_self A)).conjTranspose_mul_mul_same K
    rwa [hKh] at this
  have hsplit : K * (1 - G⁻¹) * K = K * K - K * G⁻¹ * K := by
    rw [Matrix.mul_sub K 1 G⁻¹, Matrix.mul_one, Matrix.sub_mul]
  have d1 := re_nonneg_of_psd p1 i
  have d2 := re_nonneg_of_psd p2 i
  rw [hsplit, Matrix.sub_apply, Complex.sub_re] at d2
  have eK : (K i i).re = (W i i).re - y := by
    simp [hK, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq]
  have e1 : ((K * G⁻¹ * K) i i).re = (W i i).re - y - (1 + y) + (1 + y) ^ 2 * (G⁻¹ i i).re := by
    rw [hKGK, Matrix.add_apply, Matrix.sub_apply, Complex.add_re, Complex.sub_re, eK,
      Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, smul_eq_mul,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.one_re, mul_one]
  have e2 : ((K * K) i i).re = ((W * W) i i).re - 2 * y * (W i i).re + y ^ 2 := by
    rw [hKK, Matrix.add_apply, Matrix.sub_apply, Complex.add_re, Complex.sub_re,
      Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, smul_eq_mul,
      Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.one_re, mul_one]
  rw [e1] at d1 d2
  rw [e2] at d2
  constructor <;> nlinarith

lemma inv_diag_unit {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (i : Fin m) :
    0 ≤ ((1 + Aᴴ * A)⁻¹ i i).re ∧ ((1 + Aᴴ * A)⁻¹ i i).re ≤ 1 := by
  have a := re_nonneg_of_psd (gram_posDef A).inv.posSemidef i
  have b := re_nonneg_of_psd (one_sub_inv_psd (Aᴴ * A) (Matrix.posSemidef_conjTranspose_mul_self A)) i
  rw [Matrix.sub_apply, Matrix.one_apply_eq, Complex.sub_re, Complex.one_re] at b
  exact ⟨a, by linarith⟩

-- ==== C4 part C: Gaussian moments of W = AᴴA ====

lemma WA_apply {m : ℕ} (τ : ℝ) (z : EuclideanSpace ℝ (Fin m × Fin m)) (i j : Fin m) :
    ((matA τ z)ᴴ * matA τ z) i j
      = (((τ / Real.sqrt m) ^ 2 * ∑ k, z (k, i) * z (k, j) : ℝ) : ℂ) := by
  rw [Matrix.mul_apply, Finset.mul_sum]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [matA, Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_ofReal]
  push_cast; ring

lemma w1_eq {m : ℕ} (τ : ℝ) (z : EuclideanSpace ℝ (Fin m × Fin m)) (i : Fin m) :
    (((matA τ z)ᴴ * matA τ z) i i).re = (τ / Real.sqrt m) ^ 2 * ∑ k, z (k, i) ^ 2 := by
  rw [WA_apply, Complex.ofReal_re]
  simp only [sq]

lemma w2_eq {m : ℕ} (τ : ℝ) (z : EuclideanSpace ℝ (Fin m × Fin m)) (i : Fin m) :
    (((matA τ z)ᴴ * matA τ z * ((matA τ z)ᴴ * matA τ z)) i i).re
      = (τ / Real.sqrt m) ^ 4 * ∑ j, ∑ k, ∑ l, z (k, i) * z (k, j) * z (l, i) * z (l, j) := by
  rw [Matrix.mul_apply, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [WA_apply, WA_apply, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hs : ∑ k, z (k, j) * z (k, i) = ∑ k, z (k, i) * z (k, j) :=
    Finset.sum_congr rfl fun k _ => mul_comm _ _
  rw [hs, show ∀ a b : ℝ, (a ^ 2 * b) * (a ^ 2 * b) = a ^ 4 * (b * b) from fun a b => by ring,
    Finset.sum_mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

lemma mono_val {m : ℕ} (i j k l : Fin m) :
    ∫ z : EuclideanSpace ℝ (Fin m × Fin m), z (k, i) * z (k, j) * z (l, i) * z (l, j)
        ∂(stdGaussian (EuclideanSpace ℝ (Fin m × Fin m)))
      = (if j = i then 1 else 0) + (if k = l then 1 else 0) * (1 + if j = i then 1 else 0) := by
  by_cases hj : j = i <;> by_cases hk : k = l
  · subst hj; subst hk
    have e : ∀ z : EuclideanSpace ℝ (Fin m × Fin m),
        z (k, j) * z (k, j) * z (k, j) * z (k, j) = z (k, j) ^ 4 := fun z => by ring
    simp_rw [e]; rw [E2C4.mom4]; norm_num
  · subst hj
    have e : ∀ z : EuclideanSpace ℝ (Fin m × Fin m),
        z (k, j) * z (k, j) * z (l, j) * z (l, j) = z (k, j) ^ 2 * z (l, j) ^ 2 := fun z => by ring
    simp_rw [e]
    rw [E2C4.mom22 _ _ (fun h => hk (Prod.ext_iff.1 h).1)]
    simp [hk]
  · subst hk
    have e : ∀ z : EuclideanSpace ℝ (Fin m × Fin m),
        z (k, i) * z (k, j) * z (k, i) * z (k, j) = z (k, i) ^ 2 * z (k, j) ^ 2 := fun z => by ring
    simp_rw [e]
    rw [E2C4.mom22 _ _ (fun h => hj (Prod.ext_iff.1 h).2.symm)]
    simp [hj]
  · rw [E2C4.mono_odd (k, i) (k, j) (l, i) (l, j) (fun h => hj (Prod.ext_iff.1 h).2)
      (fun h => hk (Prod.ext_iff.1 h).1.symm) (fun h => hk (Prod.ext_iff.1 h).1.symm)]
    simp [hj, hk]

lemma Ew1 {m : ℕ} (hm : 0 < m) (τ : ℝ) (i : Fin m) :
    ∫ z, (((matA τ z)ᴴ * matA τ z) i i).re ∂(stdGaussian (EuclideanSpace ℝ (Fin m × Fin m)))
      = τ ^ 2 := by
  simp_rw [w1_eq]
  rw [integral_const_mul, integral_finset_sum Finset.univ (fun k _ => E2C4.intg_pow (k, i) 2)]
  simp_rw [E2C4.mom2]
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, div_pow,
    Real.sq_sqrt hm'.le]
  field_simp

lemma Ew2 {m : ℕ} (hm : 0 < m) (τ : ℝ) (i : Fin m) :
    ∫ z, (((matA τ z)ᴴ * matA τ z * ((matA τ z)ᴴ * matA τ z)) i i).re
        ∂(stdGaussian (EuclideanSpace ℝ (Fin m × Fin m)))
      = τ ^ 4 * (2 + 1 / m) := by
  simp_rw [w2_eq]
  rw [integral_const_mul, integral_finset_sum Finset.univ (fun j _ => integrable_finset_sum Finset.univ
    fun k _ => integrable_finset_sum Finset.univ fun l _ => E2C4.intg_mono4 (k, i) (k, j) (l, i) (l, j))]
  have hin : ∀ j, ∫ z : EuclideanSpace ℝ (Fin m × Fin m), ∑ k, ∑ l,
      z (k, i) * z (k, j) * z (l, i) * z (l, j) ∂(stdGaussian (EuclideanSpace ℝ (Fin m × Fin m)))
      = ∑ k : Fin m, ∑ l : Fin m, ((if j = i then (1 : ℝ) else 0)
          + (if k = l then (1 : ℝ) else 0) * (1 + if j = i then (1 : ℝ) else 0)) := by
    intro j
    rw [integral_finset_sum Finset.univ (fun k _ => integrable_finset_sum Finset.univ fun l _ =>
      E2C4.intg_mono4 (k, i) (k, j) (l, i) (l, j))]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_finset_sum Finset.univ (fun l _ => E2C4.intg_mono4 (k, i) (k, j) (l, i) (l, j))]
    exact Finset.sum_congr rfl fun l _ => mono_val i j k l
  simp_rw [hin]
  simp only [Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Finset.sum_ite_eq']
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [div_pow, show Real.sqrt m ^ 4 = (Real.sqrt m ^ 2) ^ 2 by ring, Real.sq_sqrt hm'.le]
  field_simp
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

-- ==== C4: expectation bounds for g = re ((1 + AᴴA)⁻¹)_ii ====

open scoped Matrix.Norms.Frobenius in
lemma g_cont {m : ℕ} (τ : ℝ) (i : Fin m) :
    Continuous (fun z : EuclideanSpace ℝ (Fin m × Fin m) => ((1 + (matA τ z)ᴴ * matA τ z)⁻¹ i i).re) := by
  classical
  have : CompleteSpace (Matrix (Fin m) (Fin m) ℂ) := FiniteDimensional.complete ℝ _
  let LA : EuclideanSpace ℝ (Fin m × Fin m) →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ :=
    { toFun := matA τ
      map_add' := fun x y => by ext i j; simp [matA, mul_add]
      map_smul' := fun c x => by ext i j; simp [matA]; ring }
  let LH : Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ :=
    { toFun := Matrix.conjTranspose
      map_add' := Matrix.conjTranspose_add
      map_smul' := fun c A => by ext i j; simp }
  let Lev : Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] ℝ :=
    { toFun := fun M => (M i i).re
      map_add' := fun M N => by simp
      map_smul' := fun c M => by simp }
  have hA : Differentiable ℝ (fun z : EuclideanSpace ℝ (Fin m × Fin m) => matA τ z) := LA.toContinuousLinearMap.differentiable
  have hAH : Differentiable ℝ (fun z : EuclideanSpace ℝ (Fin m × Fin m) => (matA τ z)ᴴ) :=
    LH.toContinuousLinearMap.differentiable.comp hA
  have hR : Differentiable ℝ (fun z : EuclideanSpace ℝ (Fin m × Fin m) => (1 + (matA τ z)ᴴ * matA τ z)⁻¹) := by
    intro p
    simp_rw [Matrix.nonsing_inv_eq_ringInverse]
    exact (differentiableAt_inverse (gram_posDef _).isUnit).comp p
      ((differentiable_const _).add (hAH.mul hA) p)
  exact Lev.continuous_of_finiteDimensional.comp hR.continuous

lemma g_int {m : ℕ} (τ : ℝ) (i : Fin m) :
    Integrable (fun z : EuclideanSpace ℝ (Fin m × Fin m) => ((1 + (matA τ z)ᴴ * matA τ z)⁻¹ i i).re)
      (stdGaussian (EuclideanSpace ℝ (Fin m × Fin m))) :=
  integrableOn_univ.1 (Measure.integrableOn_of_bounded (M := 1) (measure_ne_top _ _)
    (g_cont τ i).measurable.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
      have h := inv_diag_unit (matA τ z) i
      rw [Real.norm_eq_abs, abs_le]; constructor <;> linarith [h.1, h.2]))

lemma w1_int {m : ℕ} (τ : ℝ) (i : Fin m) :
    Integrable (fun z : EuclideanSpace ℝ (Fin m × Fin m) => (((matA τ z)ᴴ * matA τ z) i i).re)
      (stdGaussian (EuclideanSpace ℝ (Fin m × Fin m))) := by
  simp_rw [w1_eq]
  exact (integrable_finset_sum Finset.univ fun k _ => E2C4.intg_pow (k, i) 2).const_mul _

lemma w2_int {m : ℕ} (τ : ℝ) (i : Fin m) :
    Integrable (fun z : EuclideanSpace ℝ (Fin m × Fin m) =>
      (((matA τ z)ᴴ * matA τ z * ((matA τ z)ᴴ * matA τ z)) i i).re)
      (stdGaussian (EuclideanSpace ℝ (Fin m × Fin m))) := by
  simp_rw [w2_eq]
  exact (integrable_finset_sum Finset.univ fun j _ => integrable_finset_sum Finset.univ
    fun k _ => integrable_finset_sum Finset.univ fun l _ =>
      E2C4.intg_mono4 (k, i) (k, j) (l, i) (l, j)).const_mul _

lemma Eg_lower {m : ℕ} (hm : 0 < m) (τ : ℝ) (i : Fin m) :
    1 + τ ^ 2 ≤ (1 + τ ^ 2) ^ 2 * ∫ z, ((1 + (matA τ z)ᴴ * matA τ z)⁻¹ i i).re
      ∂(stdGaussian (EuclideanSpace ℝ (Fin m × Fin m))) := by
  have hmono := integral_mono (μ := stdGaussian (EuclideanSpace ℝ (Fin m × Fin m)))
    ((integrable_const (1 + 2 * τ ^ 2)).sub (w1_int τ i))
    ((g_int τ i).const_mul ((1 + τ ^ 2) ^ 2))
    (fun z => by
      have := (inv_diag_bounds (matA τ z) i (τ ^ 2)).1
      simp only [Pi.sub_apply]; linarith)
  have eL : ∫ x, (1 + 2 * τ ^ 2 - (((matA τ x)ᴴ * matA τ x) i i).re)
      ∂(stdGaussian (EuclideanSpace ℝ (Fin m × Fin m))) = 1 + 2 * τ ^ 2 - τ ^ 2 := by
    rw [integral_sub (integrable_const _) (w1_int τ i), integral_const, Ew1 hm]; simp
  simp only [Pi.sub_apply] at hmono
  rw [eL, integral_const_mul] at hmono
  linarith

lemma Eg_upper {m : ℕ} (hm : 0 < m) (τ : ℝ) (i : Fin m) :
    (1 + 2 * τ ^ 2) ^ 2 * ∫ z, ((1 + (matA τ z)ᴴ * matA τ z)⁻¹ i i).re
      ∂(stdGaussian (EuclideanSpace ℝ (Fin m × Fin m)))
      ≤ τ ^ 4 * (2 + 1 / m) - (1 + 2 * (2 * τ ^ 2)) * τ ^ 2 + (1 + 2 * τ ^ 2) ^ 2 := by
  set c1 : ℝ := 1 + 2 * (2 * τ ^ 2)
  set c2 : ℝ := (1 + 2 * τ ^ 2) ^ 2
  have hI1 : Integrable (fun x : EuclideanSpace ℝ (Fin m × Fin m) =>
      (((matA τ x)ᴴ * matA τ x * ((matA τ x)ᴴ * matA τ x)) i i).re
        - c1 * (((matA τ x)ᴴ * matA τ x) i i).re)
      (stdGaussian (EuclideanSpace ℝ (Fin m × Fin m))) :=
    (w2_int τ i).sub ((w1_int τ i).const_mul c1)
  have hI2 : Integrable (fun x : EuclideanSpace ℝ (Fin m × Fin m) =>
      (((matA τ x)ᴴ * matA τ x * ((matA τ x)ᴴ * matA τ x)) i i).re
        - c1 * (((matA τ x)ᴴ * matA τ x) i i).re + c2)
      (stdGaussian (EuclideanSpace ℝ (Fin m × Fin m))) := hI1.add (integrable_const c2)
  have hmono := integral_mono (μ := stdGaussian (EuclideanSpace ℝ (Fin m × Fin m)))
    ((g_int τ i).const_mul c2) hI2
    (fun z => (inv_diag_bounds (matA τ z) i (2 * τ ^ 2)).2)
  have eU : ∫ x, ((((matA τ x)ᴴ * matA τ x * ((matA τ x)ᴴ * matA τ x)) i i).re
        - c1 * (((matA τ x)ᴴ * matA τ x) i i).re + c2)
      ∂(stdGaussian (EuclideanSpace ℝ (Fin m × Fin m))) = τ ^ 4 * (2 + 1 / m) - c1 * τ ^ 2 + c2 := by
    rw [integral_add hI1 (integrable_const _), integral_sub (w2_int τ i) ((w1_int τ i).const_mul c1),
      integral_const_mul, integral_const, Ew1 hm, Ew2 hm]; simp
  rw [eU, integral_const_mul] at hmono
  exact hmono

/-- Numeric window at `τ = 5/4`, `m ≥ 8`. -/
lemma Eg_window {m : ℕ} (hm : 8 ≤ m) (i : Fin m) :
    5 / 14 ≤ ∫ z, ((1 + (matA (5 / 4) z)ᴴ * matA (5 / 4) z)⁻¹ i i).re
      ∂(stdGaussian (EuclideanSpace ℝ (Fin m × Fin m))) ∧
    ∫ z, ((1 + (matA (5 / 4) z)ᴴ * matA (5 / 4) z)⁻¹ i i).re
      ∂(stdGaussian (EuclideanSpace ℝ (Fin m × Fin m))) ≤ 9 / 14 := by
  have hm0 : 0 < m := by omega
  have h1 := Eg_lower hm0 (5 / 4) i
  have h2 := Eg_upper hm0 (5 / 4) i
  set I := ∫ z, ((1 + (matA (5 / 4) z)ᴴ * matA (5 / 4) z)⁻¹ i i).re
      ∂(stdGaussian (EuclideanSpace ℝ (Fin m × Fin m)))
  have hm8 : (8 : ℝ) ≤ m := by exact_mod_cast hm
  have hinv : 1 / (m : ℝ) ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) hm8
  have hinv0 : 0 ≤ 1 / (m : ℝ) := by positivity
  constructor <;> nlinarith

-- ==== C4 part D: symmetry, off-diagonal vanishing, mean of F2 ====

open scoped Matrix.Norms.Frobenius in
lemma gr_diff {m : ℕ} (τ : ℝ) :
    Differentiable ℝ (fun z : EuclideanSpace ℝ (Fin m × Fin m) => gr (matA τ z)) := by
  classical
  have : CompleteSpace (Matrix (Fin m) (Fin m) ℂ) := FiniteDimensional.complete ℝ _
  let LA : EuclideanSpace ℝ (Fin m × Fin m) →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ :=
    { toFun := matA τ
      map_add' := fun x y => by ext i j; simp [matA, mul_add]
      map_smul' := fun c x => by ext i j; simp [matA]; ring }
  let LH : Matrix (Fin m) (Fin m) ℂ →ₗ[ℝ] Matrix (Fin m) (Fin m) ℂ :=
    { toFun := Matrix.conjTranspose
      map_add' := Matrix.conjTranspose_add
      map_smul' := fun c A => by ext i j; simp }
  let LB : (Matrix (Fin m) (Fin m) ℂ × Matrix (Fin m) (Fin m) ℂ) ×
      (Matrix (Fin m) (Fin m) ℂ × Matrix (Fin m) (Fin m) ℂ) →ₗ[ℝ]
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℂ :=
    { toFun := fun x => Matrix.fromBlocks x.1.1 x.1.2 x.2.1 x.2.2
      map_add' := fun x y => (Matrix.fromBlocks_add _ _ _ _ _ _ _ _).symm
      map_smul' := fun c x => (Matrix.fromBlocks_smul _ _ _ _ _).symm }
  have hA : Differentiable ℝ (fun z : EuclideanSpace ℝ (Fin m × Fin m) => matA τ z) :=
    LA.toContinuousLinearMap.differentiable
  have hAH : Differentiable ℝ (fun z : EuclideanSpace ℝ (Fin m × Fin m) => (matA τ z)ᴴ) := by
    have h := LH.toContinuousLinearMap.differentiable.comp hA
    exact h
  have hR : Differentiable ℝ
      (fun z : EuclideanSpace ℝ (Fin m × Fin m) => (1 + (matA τ z)ᴴ * matA τ z)⁻¹) := by
    intro p
    simp_rw [Matrix.nonsing_inv_eq_ringInverse]
    exact (differentiableAt_inverse (gram_posDef _).isUnit).comp p
      ((differentiable_const _).add (hAH.mul hA) p)
  have hblk : (fun z : EuclideanSpace ℝ (Fin m × Fin m) => gr (matA τ z)) = fun z => LB
      (((1 + (matA τ z)ᴴ * matA τ z)⁻¹, (1 + (matA τ z)ᴴ * matA τ z)⁻¹ * (matA τ z)ᴴ),
       (matA τ z * (1 + (matA τ z)ᴴ * matA τ z)⁻¹,
        matA τ z * (1 + (matA τ z)ᴴ * matA τ z)⁻¹ * (matA τ z)ᴴ)) := by
    funext z; rw [gr_blocks]; rfl
  rw [hblk]
  exact LB.toContinuousLinearMap.differentiable.comp
    ((hR.prodMk (hR.mul hAH)).prodMk ((hA.mul hR).prodMk ((hA.mul hR).mul hAH)))

lemma gr_entry_sq {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (p q : Fin m ⊕ Fin m) :
    ‖gr A p q‖ ^ 2 ≤ m := by
  have h1 : fr2 (gr A) = m := by
    unfold fr2
    rw [(gr_isHermitian A).eq, gr_idem, gr_trace]; simp
  have h2 : ‖gr A p q‖ ^ 2 ≤ fr2 (gr A) := by
    rw [fr2_eq_sum]
    calc ‖gr A p q‖ ^ 2 ≤ ∑ j, ‖gr A p j‖ ^ 2 :=
          Finset.single_le_sum (f := fun j => ‖gr A p j‖ ^ 2) (fun j _ => by positivity)
            (Finset.mem_univ q)
      _ ≤ ∑ i, ∑ j, ‖gr A i j‖ ^ 2 :=
          Finset.single_le_sum (f := fun i => ∑ j, ‖gr A i j‖ ^ 2) (fun i _ => by positivity)
            (Finset.mem_univ p)
  linarith

lemma re_int {m : ℕ} (τ : ℝ) (p q : Fin m ⊕ Fin m) :
    Integrable (fun z : EuclideanSpace ℝ (Fin m × Fin m) => (gr (matA τ z) p q).re)
      (stdGaussian (EuclideanSpace ℝ (Fin m × Fin m))) := by
  have hc : Continuous (fun z : EuclideanSpace ℝ (Fin m × Fin m) => (gr (matA τ z) p q).re) :=
    Complex.continuous_re.comp ((gr_diff τ).continuous.matrix_elem p q)
  exact integrableOn_univ.1 (Measure.integrableOn_of_bounded (M := m + 1) (measure_ne_top _ _)
    hc.measurable.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
      have h := gr_entry_sq (matA τ z) p q
      have h2 := Complex.abs_re_le_norm (gr (matA τ z) p q)
      rw [Real.norm_eq_abs]; nlinarith [norm_nonneg (gr (matA τ z) p q)]))

lemma im_int {m : ℕ} (τ : ℝ) (p q : Fin m ⊕ Fin m) :
    Integrable (fun z : EuclideanSpace ℝ (Fin m × Fin m) => (gr (matA τ z) p q).im)
      (stdGaussian (EuclideanSpace ℝ (Fin m × Fin m))) := by
  have hc : Continuous (fun z : EuclideanSpace ℝ (Fin m × Fin m) => (gr (matA τ z) p q).im) :=
    Complex.continuous_im.comp ((gr_diff τ).continuous.matrix_elem p q)
  exact integrableOn_univ.1 (Measure.integrableOn_of_bounded (M := m + 1) (measure_ne_top _ _)
    hc.measurable.aestronglyMeasurable (Filter.Eventually.of_forall fun z => by
      have h := gr_entry_sq (matA τ z) p q
      have h2 := Complex.abs_im_le_norm (gr (matA τ z) p q)
      rw [Real.norm_eq_abs]; nlinarith [norm_nonneg (gr (matA τ z) p q)]))

lemma gr_sign {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (u : Fin m ⊕ Fin m → ℂ)
    (hu : ∀ r, u r * u r = 1) (hs : ∀ r, star (u r) = u r) :
    gr (Matrix.diagonal (u ∘ Sum.inr) * A * Matrix.diagonal (u ∘ Sum.inl))
      = Matrix.diagonal u * gr A * Matrix.diagonal u := by
  set D : Matrix (Fin m) (Fin m) ℂ := Matrix.diagonal (u ∘ Sum.inl) with hDdef
  set U : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℂ := Matrix.diagonal u with hUdef
  have hDD : D * D = 1 := by
    rw [hDdef, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; exact hu _
  have hUU : U * U = 1 := by
    rw [hUdef, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext i; exact hu _
  have hDh : Dᴴ = D := by
    rw [hDdef, Matrix.diagonal_conjTranspose]; congr 1; funext i; exact hs _
  have hUh : Uᴴ = U := by
    rw [hUdef, Matrix.diagonal_conjTranspose]; congr 1; funext i; exact hs _
  have hDinv : D⁻¹ = D := Matrix.inv_eq_left_inv hDD
  have hX : grX (Matrix.diagonal (u ∘ Sum.inr) * A * D) = U * grX A * D := by
    ext r j
    rcases r with i | i
    · simp only [grX, hUdef, hDdef, Matrix.mul_diagonal, Matrix.diagonal_mul,
        Matrix.fromRows_apply_inl, Matrix.one_apply, Function.comp]
      split_ifs with h
      · subst h; rw [mul_one, hu]
      · simp
    · simp only [grX, hUdef, hDdef, Matrix.mul_diagonal, Matrix.diagonal_mul,
        Matrix.fromRows_apply_inr, Function.comp]
  unfold gr
  rw [hX, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hDh, hUh]
  set X := grX A
  have hG : D * (Xᴴ * U) * (U * X * D) = D * (Xᴴ * X) * D := by
    calc D * (Xᴴ * U) * (U * X * D) = D * (Xᴴ * (U * U) * X) * D := by
          simp only [Matrix.mul_assoc]
      _ = D * (Xᴴ * X) * D := by rw [hUU, Matrix.mul_one]
  rw [hG, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hDinv]
  calc U * X * D * (D * ((Xᴴ * X)⁻¹ * D)) * (D * (Xᴴ * U))
      = U * X * (D * D) * (Xᴴ * X)⁻¹ * (D * D) * Xᴴ * U := by simp only [Matrix.mul_assoc]
    _ = U * (X * (Xᴴ * X)⁻¹ * Xᴴ) * U := by
        rw [hDD, Matrix.mul_one, Matrix.mul_one]; simp only [Matrix.mul_assoc]

lemma off_zero {m : ℕ} (τ : ℝ) (p q : Fin m ⊕ Fin m) (hpq : p ≠ q) :
    ∫ z, (gr (matA τ z) p q).re ∂(stdGaussian (EuclideanSpace ℝ (Fin m × Fin m))) = 0 ∧
    ∫ z, (gr (matA τ z) p q).im ∂(stdGaussian (EuclideanSpace ℝ (Fin m × Fin m))) = 0 := by
  set v : Fin m ⊕ Fin m → ℝ := fun r => if r = q then -1 else 1 with hv
  have hv1 : ∀ r, v r * v r = 1 := fun r => by simp only [hv]; split_ifs <;> norm_num
  set ε : Fin m × Fin m → ℝ := fun x => v (Sum.inr x.1) * v (Sum.inl x.2) with hεd
  have hε : ∀ x, ε x * ε x = 1 := fun x => by
    have a := hv1 (Sum.inr x.1); have b := hv1 (Sum.inl x.2)
    simp only [hεd]
    calc v (Sum.inr x.1) * v (Sum.inl x.2) * (v (Sum.inr x.1) * v (Sum.inl x.2))
        = (v (Sum.inr x.1) * v (Sum.inr x.1)) * (v (Sum.inl x.2) * v (Sum.inl x.2)) := by ring
      _ = 1 := by rw [a, b, one_mul]
  have key : ∀ z, gr (matA τ (E2C4.signE ε hε z)) p q = - gr (matA τ z) p q := by
    intro z
    have hA : matA τ (E2C4.signE ε hε z)
        = Matrix.diagonal ((fun r => ((v r : ℝ) : ℂ)) ∘ Sum.inr) * matA τ z
          * Matrix.diagonal ((fun r => ((v r : ℝ) : ℂ)) ∘ Sum.inl) := by
      ext a j
      simp only [matA, E2C4.signE_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
        Function.comp, hεd]
      push_cast; ring
    rw [hA, gr_sign _ _ (fun r => by exact_mod_cast hv1 r)
      (fun r => by rw [Complex.star_def, Complex.conj_ofReal])]
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal]
    have hp : v p = 1 := by simp [hv, hpq]
    have hq : v q = -1 := by simp [hv]
    rw [hp, hq]; push_cast; ring
  exact ⟨E2C4.int_odd _ _ fun z => by rw [key, Complex.neg_re],
    E2C4.int_odd _ _ fun z => by rw [key, Complex.neg_im]⟩

lemma conjT_matA {m : ℕ} (τ : ℝ) (z : EuclideanSpace ℝ (Fin m × Fin m)) :
    (matA τ z)ᴴ = matA τ (E2C4.permE (Equiv.prodComm (Fin m) (Fin m)) z) := by
  ext i j
  simp only [matA, Matrix.conjTranspose_apply, E2C4.permE_apply, Equiv.prodComm_apply,
    Prod.swap_prod_mk, Complex.star_def, Complex.conj_ofReal]

lemma push_through {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) :
    A * (1 + Aᴴ * A)⁻¹ * Aᴴ = 1 - (1 + A * Aᴴ)⁻¹ := by
  have hu1 : IsUnit (1 + Aᴴ * A).det := (gram_posDef A).isUnit.map Matrix.detMonoidHom
  have hu2 : IsUnit (1 + A * Aᴴ).det := by
    have := (gram_posDef Aᴴ).isUnit.map Matrix.detMonoidHom
    simpa using this
  have e : (1 + A * Aᴴ) * A = A * (1 + Aᴴ * A) := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.mul_assoc]
  have h1 : A * (1 + Aᴴ * A)⁻¹ = (1 + A * Aᴴ)⁻¹ * A := by
    calc A * (1 + Aᴴ * A)⁻¹ = (1 + A * Aᴴ)⁻¹ * ((1 + A * Aᴴ) * A) * (1 + Aᴴ * A)⁻¹ := by
          rw [← Matrix.mul_assoc (1 + A * Aᴴ)⁻¹, Matrix.nonsing_inv_mul _ hu2, Matrix.one_mul]
      _ = (1 + A * Aᴴ)⁻¹ * A := by
          rw [e, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu1, Matrix.mul_one]
  rw [h1, Matrix.mul_assoc]
  have h2 : (1 + A * Aᴴ)⁻¹ * (1 + A * Aᴴ) = 1 := Matrix.nonsing_inv_mul _ hu2
  rw [Matrix.mul_add, Matrix.mul_one] at h2
  rw [eq_sub_iff_add_eq]
  exact (add_comm _ _).trans h2

lemma gr_diag_im {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (p : Fin m ⊕ Fin m) :
    (gr A p p).im = 0 := by
  have h := (gr_isHermitian A).apply p p
  rw [Complex.star_def, Complex.conj_eq_iff_im] at h
  exact h

lemma top_int {m : ℕ} (τ : ℝ) (i : Fin m) :
    ∫ z, (gr (matA τ z) (Sum.inl i) (Sum.inl i)).re
      ∂(stdGaussian (EuclideanSpace ℝ (Fin m × Fin m)))
      = ∫ z, ((1 + (matA τ z)ᴴ * matA τ z)⁻¹ i i).re
      ∂(stdGaussian (EuclideanSpace ℝ (Fin m × Fin m))) := by
  congr 1; funext z; rw [gr_blocks, Matrix.fromBlocks_apply₁₁]

lemma bot_int {m : ℕ} (τ : ℝ) (i : Fin m) :
    ∫ z, (gr (matA τ z) (Sum.inr i) (Sum.inr i)).re
      ∂(stdGaussian (EuclideanSpace ℝ (Fin m × Fin m)))
      = 1 - ∫ z, ((1 + (matA τ z)ᴴ * matA τ z)⁻¹ i i).re
      ∂(stdGaussian (EuclideanSpace ℝ (Fin m × Fin m))) := by
  have hpt : ∀ z, (gr (matA τ z) (Sum.inr i) (Sum.inr i)).re
      = 1 - ((1 + (matA τ (E2C4.permE (Equiv.prodComm (Fin m) (Fin m)) z))ᴴ
          * matA τ (E2C4.permE (Equiv.prodComm (Fin m) (Fin m)) z))⁻¹ i i).re := by
    intro z
    rw [gr_blocks, Matrix.fromBlocks_apply₂₂, push_through, ← conjT_matA,
      Matrix.conjTranspose_conjTranspose]
    simp [Matrix.sub_apply]
  simp_rw [hpt]
  rw [E2C4.int_iso (E2C4.permE (Equiv.prodComm (Fin m) (Fin m)))
    (fun z => 1 - ((1 + (matA τ z)ᴴ * matA τ z)⁻¹ i i).re),
    integral_sub (integrable_const 1) (g_int τ i)]
  simp

lemma F2_expand {m : ℕ} (τ : ℝ)
    (x : EuclideanSpace ℝ (Fin m × Fin m) × EuclideanSpace ℝ (Fin m × Fin m)) :
    F2 τ x = ∑ p, ∑ q, ((gr (matA τ x.1) p q).re * (gr (matA τ x.2) q p).re
      - (gr (matA τ x.1) p q).im * (gr (matA τ x.2) q p).im) := by
  simp only [F2, Matrix.trace, Matrix.diag, Matrix.mul_apply, Complex.re_sum, Complex.mul_re]

lemma term_int {m : ℕ} (τ : ℝ) (p q : Fin m ⊕ Fin m) :
    ∫ x, ((gr (matA τ x.1) p q).re * (gr (matA τ x.2) q p).re
      - (gr (matA τ x.1) p q).im * (gr (matA τ x.2) q p).im)
      ∂((stdGaussian (EuclideanSpace ℝ (Fin m × Fin m))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin m × Fin m))))
    = (∫ z, (gr (matA τ z) p q).re ∂(stdGaussian (EuclideanSpace ℝ (Fin m × Fin m))))
        * (∫ z, (gr (matA τ z) q p).re ∂(stdGaussian (EuclideanSpace ℝ (Fin m × Fin m))))
      - (∫ z, (gr (matA τ z) p q).im ∂(stdGaussian (EuclideanSpace ℝ (Fin m × Fin m))))
        * (∫ z, (gr (matA τ z) q p).im ∂(stdGaussian (EuclideanSpace ℝ (Fin m × Fin m)))) := by
  rw [integral_sub ((re_int τ p q).mul_prod (re_int τ q p)) ((im_int τ p q).mul_prod (im_int τ q p)),
    integral_prod_mul (fun z => (gr (matA τ z) p q).re) (fun z => (gr (matA τ z) q p).re),
    integral_prod_mul (fun z => (gr (matA τ z) p q).im) (fun z => (gr (matA τ z) q p).im)]

lemma EF2_eq {m : ℕ} (τ : ℝ) :
    ∫ x, F2 (m := m) τ x ∂((stdGaussian (EuclideanSpace ℝ (Fin m × Fin m))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin m × Fin m))))
      = ∑ p, (∫ z, (gr (matA τ z) p p).re ∂(stdGaussian (EuclideanSpace ℝ (Fin m × Fin m)))) ^ 2 := by
  have hint : ∀ p q, Integrable (fun x : EuclideanSpace ℝ (Fin m × Fin m) × EuclideanSpace ℝ (Fin m × Fin m) =>
      (gr (matA τ x.1) p q).re * (gr (matA τ x.2) q p).re
        - (gr (matA τ x.1) p q).im * (gr (matA τ x.2) q p).im)
      ((stdGaussian (EuclideanSpace ℝ (Fin m × Fin m))).prod
        (stdGaussian (EuclideanSpace ℝ (Fin m × Fin m)))) := fun p q =>
    ((re_int τ p q).mul_prod (re_int τ q p)).sub ((im_int τ p q).mul_prod (im_int τ q p))
  simp_rw [F2_expand]
  rw [integral_finset_sum]
  swap
  · exact fun p _ => integrable_finset_sum _ fun q _ => hint p q
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_finset_sum]
  swap
  · exact fun q _ => hint p q
  simp_rw [term_int]
  rw [Finset.sum_eq_single p (fun q _ hq => by
      rw [(off_zero τ p q (Ne.symm hq)).1, (off_zero τ p q (Ne.symm hq)).2]; ring)
    (fun h => absurd (Finset.mem_univ p) h)]
  simp_rw [gr_diag_im]
  simp; ring

theorem C4 : C4_mean := by
  refine ⟨5 / 4, by norm_num, 8, fun m hm => ?_⟩
  rw [EF2_eq, Fintype.sum_sum_type]
  simp_rw [top_int, bot_int]
  rw [← Finset.sum_add_distrib]
  have hw := fun i => Eg_window hm i
  constructor
  · calc (m : ℝ) / 2 = ∑ _i : Fin m, (1 / 2 : ℝ) := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun i _ => by
          nlinarith [sq_nonneg (∫ z, ((1 + (matA (5 / 4) z)ᴴ * matA (5 / 4) z)⁻¹ i i).re
            ∂(stdGaussian (EuclideanSpace ℝ (Fin m × Fin m))) - 1 / 2)]
  · calc _ ≤ ∑ _i : Fin m, (1 / 2 + 2 / 49 : ℝ) := Finset.sum_le_sum fun i _ => by
          nlinarith [(hw i).1, (hw i).2]
      _ ≤ 13 * (m : ℝ) / 24 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have : (0 : ℝ) ≤ m := by positivity
          nlinarith

lemma trace_reidx {r : ℕ} (M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) ℂ) :
    (Matrix.reindex finSumFinEquiv finSumFinEquiv M).trace = M.trace := by
  simp only [Matrix.trace, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.diag_apply]
  exact Equiv.sum_comp finSumFinEquiv.symm (fun i => M i i)

lemma reidx_half {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) :
    ShadowTomography.QuantumLB.IsHalfProjector
      (Matrix.reindex finSumFinEquiv finSumFinEquiv (gr A)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (gr_isHermitian A).submatrix _
  · rw [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, gr_idem]
  · rw [trace_reidx, gr_trace]
    push_cast
    ring

lemma reidx_pair {r : ℕ} (A B : Matrix (Fin r) (Fin r) ℂ) :
    (Matrix.reindex finSumFinEquiv finSumFinEquiv (gr A) *
        ShadowTomography.QuantumLB.rhoState
          (Matrix.reindex finSumFinEquiv finSumFinEquiv (gr B))).trace.re
      = (2 / ((r + r : ℕ) : ℝ)) * (gr A * gr B).trace.re := by
  unfold ShadowTomography.QuantumLB.rhoState
  rw [Matrix.mul_smul, Matrix.trace_smul, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, ← Matrix.reindex_apply, trace_reidx, smul_eq_mul]
  have : ((2 : ℂ) / ((r + r : ℕ) : ℂ)) = (((2 / ((r + r : ℕ) : ℝ)) : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.re_ofReal_mul]

lemma kappa_bounds (L : NNReal) :
    0 < 1 / (288 * Real.pi ^ 2 * ((L + 1 : NNReal) : ℝ) ^ 2) ∧
      1 / (288 * Real.pi ^ 2 * ((L + 1 : NNReal) : ℝ) ^ 2) ≤ 1 / 288 := by
  have hL : (1 : ℝ) ≤ ((L + 1 : NNReal) : ℝ) := by
    simp only [NNReal.coe_add, NNReal.coe_one]; linarith [L.coe_nonneg]
  have hpi : (1 : ℝ) ≤ Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
  have hL2 : (1 : ℝ) ≤ ((L + 1 : NNReal) : ℝ) ^ 2 := by nlinarith
  have hd : (288 : ℝ) ≤ 288 * Real.pi ^ 2 * ((L + 1 : NNReal) : ℝ) ^ 2 := by nlinarith
  constructor
  · positivity
  · exact one_div_le_one_div_of_le (by norm_num) hd

lemma count_bound (κ : ℝ) (hκ : 0 < κ) (r K : ℕ) (hr : 2 / κ ≤ (r : ℝ)) (hr1 : 1 ≤ r)
    (hK : (K : ℝ) ≤ Real.exp (κ / 16) ^ ((r + r) ^ 2)) :
    (K : ℝ) ^ 2 * (2 * Real.exp (-κ * (r : ℝ) ^ 2)) < 1 := by
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have he : Real.exp (κ / 16) ^ ((r + r) ^ 2) = Real.exp (κ * (r : ℝ) ^ 2 / 4) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [he] at hK
  have hK2 : (K : ℝ) ^ 2 ≤ Real.exp (κ * (r : ℝ) ^ 2 / 2) := by
    calc (K : ℝ) ^ 2 ≤ Real.exp (κ * (r : ℝ) ^ 2 / 4) ^ 2 := pow_le_pow_left₀ hK0 hK 2
      _ = Real.exp (κ * (r : ℝ) ^ 2 / 2) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hrr : (r : ℝ) ≤ (r : ℝ) ^ 2 := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr1
    nlinarith
  have hkr : 2 ≤ κ * (r : ℝ) ^ 2 := by
    have h1 : 2 ≤ κ * r := by rw [div_le_iff₀ hκ] at hr; linarith
    nlinarith
  have hprod : Real.exp (κ * (r : ℝ) ^ 2 / 2) * (2 * Real.exp (-κ * (r : ℝ) ^ 2))
      = 2 * Real.exp (-(κ * (r : ℝ) ^ 2 / 2)) := by
    rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  have hsmall : Real.exp (-(κ * (r : ℝ) ^ 2 / 2)) ≤ Real.exp (-1) :=
    Real.exp_le_exp.2 (by linarith)
  have he1 : Real.exp (-1) < 1 / 2 := by
    have := Real.exp_one_gt_d9
    rw [Real.exp_neg, inv_lt_comm₀ (Real.exp_pos 1) (by norm_num)]; norm_num; linarith
  calc (K : ℝ) ^ 2 * (2 * Real.exp (-κ * (r : ℝ) ^ 2))
      ≤ Real.exp (κ * (r : ℝ) ^ 2 / 2) * (2 * Real.exp (-κ * (r : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_right hK2 (by positivity)
    _ = 2 * Real.exp (-(κ * (r : ℝ) ^ 2 / 2)) := hprod
    _ < 1 := by linarith

open ShadowTomography.QuantumLB in
theorem eq2_of_children (h1 : C1_gauss_conc) (h3 : C3_F_lipschitz) (h4 : C4_mean) :
    ∃ c : ℝ, 1 < c ∧ c < 2 ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ P : Fin ⌊c ^ (N ^ 2)⌋₊ → Matrix (Fin N) (Fin N) ℂ,
        (∀ i, IsHalfProjector (P i)) ∧
        ∀ i j, i ≠ j → |(P i * rhoState (P j)).trace.re - 1 / 2| ≤ 1 / 12 := by
  obtain ⟨τ, hτ, m₀, hm₀⟩ := h4
  obtain ⟨L, hL⟩ := h3 τ hτ
  set L' : NNReal := L + 1 with hL'
  set κ : ℝ := 1 / (288 * Real.pi ^ 2 * (L' : ℝ) ^ 2) with hκdef
  obtain ⟨hκ0, hκ1⟩ := kappa_bounds L
  refine ⟨Real.exp (κ / 16), ?_, ?_, 2 * (m₀ + ⌈2 / κ⌉₊ + 1), ?_⟩
  · rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (div_pos hκ0 (by norm_num))
  · have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_lt_exp.2 (by linarith)
  intro N hN hev
  obtain ⟨r, rfl⟩ := hev
  have hr0 : m₀ ≤ r := by omega
  have hr1 : 1 ≤ r := by omega
  have hrc : ⌈2 / κ⌉₊ ≤ r := by omega
  have hr2 : 2 / κ ≤ (r : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hrc)
  set μ := stdGaussian (EuclideanSpace ℝ (Fin r × Fin r))
  set mean := ∫ p, F2 (m := r) τ p ∂(μ.prod μ) with hmean
  obtain ⟨hlo, hhi⟩ := hm₀ r hr0
  obtain ⟨hdiff, hlip⟩ := hL r (by omega)
  have hlip' : LipschitzWith L' (F2 (m := r) τ) := hlip.weaken (by simp [hL'])
  have hcont : Continuous (F2 (m := r) τ) := hlip.continuous
  set Bad : Set (EuclideanSpace ℝ (Fin r × Fin r) × EuclideanSpace ℝ (Fin r × Fin r)) :=
    {p | (r : ℝ) / 24 ≤ |F2 (m := r) τ p - mean|} with hBad
  have hBm : MeasurableSet Bad :=
    measurableSet_le measurable_const ((hcont.sub continuous_const).abs.measurable)
  have hbdd : ∃ M : ℝ, ∀ p, |F2 (m := r) τ p| ≤ M := ⟨r, fun p => by
    have a := trace_gr_mul_nonneg (matA τ p.1) (matA τ p.2)
    have b := trace_gr_mul (matA τ p.1) (matA τ p.2)
    have c := fr2_nonneg (gr (matA τ p.1) - gr (matA τ p.2))
    show |(gr (matA τ p.1) * gr (matA τ p.2)).trace.re| ≤ r
    rw [abs_of_nonneg a]; linarith⟩
  have hconc := h1 (Fin r × Fin r) (F2 (m := r) τ) L' hdiff hlip' hbdd ((r : ℝ) / 24)
    (by have : (0 : ℝ) < r := by exact_mod_cast hr1
        positivity)
  have hexp : -(2 * ((r : ℝ) / 24) ^ 2) / (Real.pi ^ 2 * (L' : ℝ) ^ 2) = -κ * (r : ℝ) ^ 2 := by
    rw [hκdef]; field_simp; ring
  rw [hexp] at hconc
  have hK : ((⌊Real.exp (κ / 16) ^ ((r + r) ^ 2)⌋₊ : ℕ) : ℝ) ≤ Real.exp (κ / 16) ^ ((r + r) ^ 2) :=
    Nat.floor_le (by positivity)
  obtain ⟨x, hx⟩ := C5 _ μ Bad hBm _ _ hconc (count_bound κ hκ0 r _ hr2 hr1 hK)
  refine ⟨fun i => Matrix.reindex finSumFinEquiv finSumFinEquiv (gr (matA τ (x i))),
    fun i => reidx_half _, ?_⟩
  intro i j hij
  have hnb := hx i j hij
  simp only [hBad, Set.mem_ofPred_eq, not_le] at hnb
  rw [reidx_pair]
  have hF : F2 (m := r) τ (x i, x j) = (gr (matA τ (x i)) * gr (matA τ (x j))).trace.re := rfl
  rw [← hF]
  have hrpos : (0 : ℝ) < r := by exact_mod_cast hr1
  have hcast : (((r + r : ℕ)) : ℝ) = 2 * r := by push_cast; ring
  rw [hcast]
  rw [abs_lt] at hnb
  have hval : 2 / (2 * (r : ℝ)) * F2 (m := r) τ (x i, x j) - 1 / 2
      = (F2 (m := r) τ (x i, x j) - (r : ℝ) / 2) / r := by
    field_simp
  rw [hval, abs_div, abs_of_pos hrpos, div_le_iff₀ hrpos, abs_le]
  constructor <;> nlinarith [hnb.1, hnb.2]

end E2Plan

open ShadowTomography.QuantumLB in
theorem solution :
    ∃ c : ℝ, 1 < c ∧ c < 2 ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → Even N →
      ∃ P : Fin ⌊c ^ (N ^ 2)⌋₊ → Matrix (Fin N) (Fin N) ℂ,
        (∀ i, IsHalfProjector (P i)) ∧
        ∀ i j, i ≠ j → |(P i * rhoState (P j)).trace.re - 1 / 2| ≤ 1 / 12 := by
  exact E2Plan.eq2_of_children E2Plan.C1 E2Plan.C3 E2Plan.C4
