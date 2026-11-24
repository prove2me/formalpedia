-- Prove2me | solution 1 for SongZhangKLS.cheeger_universal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T10:24:34.638586+00:00
-- url     : https://prove2.me/submissions/5d13dc79-7389-4511-9d54-8a8236bafea2

import Mathlib
import Definitions.Def_SongZhangKLS_poincareConst
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_exists_isotropicBound_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_exists_smoothGradient_localDensity_readable
import Theorems.Thm_FunctionalInequalities_Energy_LocalSlope_apply_eq_norm_gradient_readable
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_GaussianSmoothing_Basic
import Theorems.Thm_FunctionalInequalities_Probability_covariance_sq_le_variance_mul_variance_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_mean_zero_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_variance_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_exp_norm_integrable_readable
import Theorems.Thm_PhiSobBayes_lemma_6_1
import Theorems.Thm_PhiSobBayes_fact_A_22
import Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_Holds_of_compactSupport_readable
import Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_holds_iff_localSlope_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_gaussianLaw_inner_sq_readable
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_BorellRepresentation_Construction
import Definitions.Def_SongZhangKLS_cheegerPsi
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_GaussianSmoothing_normalizedDensity_tendsto_L1_readable

-- ===== from Solutions/PartA.lean =====

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace SZPartA

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [FiniteDimensional ℝ E]

/-- The support of a log-concave probability measure is convex. -/
theorem convex_support {μ : ProbabilityMeasure E} (hμ : FunctionalInequalities.KLS.LogConcave μ) :
    Convex ℝ (μ : Measure E).support := by
  intro x hx y hy a b ha hb hab
  rw [Measure.mem_support_iff_forall] at hx hy ⊢
  intro U hU
  rcases ha.eq_or_lt with rfl | ha'
  · simp at hab; subst hab; simpa using hy U (by simpa using hU)
  rcases hb.eq_or_lt with rfl | hb'
  · simp at hab; subst hab; simpa using hx U (by simpa using hU)
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  set r' := r / 2 with hr'
  have hr'pos : 0 < r' := by positivity
  have h1 := hx _ (Metric.closedBall_mem_nhds x hr'pos)
  have h2 := hy _ (Metric.closedBall_mem_nhds y hr'pos)
  have hLC := hμ _ _ (isCompact_closedBall x r') (isCompact_closedBall y r') a ha' (by linarith)
  have hsub : {z | ∃ p ∈ Metric.closedBall x r', ∃ q ∈ Metric.closedBall y r',
      z = a • p + (1 - a) • q} ⊆ U := by
    rintro z ⟨p, hp, q, hq, rfl⟩
    apply hrU
    rw [Metric.mem_ball]
    have hb1 : b = 1 - a := by linarith
    subst hb1
    have : a • p + (1 - a) • q - (a • x + (1 - a) • y) = a • (p - x) + (1 - a) • (q - y) := by
      simp only [smul_sub]; abel
    rw [dist_eq_norm, this]
    have hp' := mem_closedBall_iff_norm.1 hp
    have hq' := mem_closedBall_iff_norm.1 hq
    have hb0 : 0 ≤ 1 - a := by linarith
    calc ‖a • (p - x) + (1 - a) • (q - y)‖ ≤ ‖a • (p - x)‖ + ‖(1 - a) • (q - y)‖ := norm_add_le _ _
      _ = a * ‖p - x‖ + (1 - a) * ‖q - y‖ := by
          rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb0]
      _ ≤ a * r' + (1 - a) * r' := by
          have := mul_le_mul_of_nonneg_left hp' ha
          have := mul_le_mul_of_nonneg_left hq' hb0
          linarith
      _ = r' := by ring
      _ < r := by rw [hr']; linarith
  have hpos : 0 < (μ : Measure E) (Metric.closedBall x r') ^ a *
      (μ : Measure E) (Metric.closedBall y r') ^ (1 - a) := by
    apply ENNReal.mul_pos
    · exact (ENNReal.rpow_pos h1 (measure_ne_top _ _)).ne'
    · exact (ENNReal.rpow_pos h2 (measure_ne_top _ _)).ne'
  exact lt_of_lt_of_le (lt_of_lt_of_le hpos hLC) (measure_mono hsub)

/-- An isotropic probability law is not carried by a proper affine subspace. -/
theorem affineSpan_support_eq_top {μ : ProbabilityMeasure E}
    (hiso : FunctionalInequalities.KLS.Isotropic μ) :
    affineSpan ℝ (μ : Measure E).support = ⊤ := by
  by_contra hne
  set P := affineSpan ℝ (μ : Measure E).support with hP
  have hsuppne : ((μ : Measure E).support).Nonempty :=
    (μ : Measure E).nonempty_support (IsProbabilityMeasure.ne_zero _)
  obtain ⟨p0, hp0⟩ := hsuppne
  have hp0P : p0 ∈ P := subset_affineSpan ℝ _ hp0
  have hPne : (P : Set E).Nonempty := ⟨p0, hp0P⟩
  have hdir : P.direction ≠ ⊤ := by
    intro h
    exact hne ((AffineSubspace.direction_eq_top_iff_of_nonempty hPne).1 h)
  have horth : P.directionᗮ ≠ ⊥ := by
    intro h
    exact hdir (Submodule.orthogonal_eq_bot_iff.1 h)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot horth
  -- a.e. ⟪v, x⟫ = ⟪v, p0⟫
  have hae : ∀ᵐ x ∂(μ : Measure E), inner ℝ v x = inner ℝ v p0 := by
    filter_upwards [Measure.support_mem_ae (μ := (μ : Measure E))] with x hx
    have hxP : x ∈ P := subset_affineSpan ℝ _ hx
    have hmem : x -ᵥ p0 ∈ P.direction := AffineSubspace.vsub_mem_direction hxP hp0P
    have := Submodule.inner_right_of_mem_orthogonal hmem hv
    rw [vsub_eq_sub, inner_sub_left] at this
    rw [real_inner_comm x v, real_inner_comm p0 v]
    linarith
  have hvar : Var[fun u ↦ inner ℝ v u; (μ : Measure E)] = 0 := by
    have hcongr : (fun u ↦ inner ℝ v u) =ᵐ[(μ : Measure E)] fun _ ↦ inner ℝ v p0 := hae
    rw [ProbabilityTheory.variance_congr hcongr]
    simp [ProbabilityTheory.variance, ProbabilityTheory.evariance]
  have hcov := FunctionalInequalities.Covariance.operator_inner (μ : Measure E) v v
  rw [hiso.covariance_identity, covarianceBilin_self hiso.memLp_two, hvar] at hcov
  simp at hcov
  exact hv0 hcov

theorem interior_support_nonempty {μ : ProbabilityMeasure E}
    (hμ : FunctionalInequalities.KLS.LogConcave μ) (hiso : FunctionalInequalities.KLS.Isotropic μ) :
    (interior (μ : Measure E).support).Nonempty :=
  (convex_support hμ).interior_nonempty_iff_affineSpan_eq_top.2 (affineSpan_support_eq_top hiso)

/-- Isotropic log-concave laws are absolutely continuous. -/
theorem absolutelyContinuous {μ : ProbabilityMeasure E} (m : Measure E) [m.IsAddHaarMeasure]
    (hμ : FunctionalInequalities.KLS.LogConcave μ) (hiso : FunctionalInequalities.KLS.Isotropic μ) :
    (μ : Measure E) ≪ m := by
  obtain ⟨D⟩ := FunctionalInequalities.KLS.LogConcave.exists_smoothGradient_localDensity_readable m hμ
    (interior_support_nonempty hμ hiso)
  have h1 : (μ : Measure E) = (μ : Measure E).restrict D.Ω := by
    symm
    apply Measure.restrict_eq_self_of_ae_mem
    rw [ae_iff]
    exact D.compl_null
  rw [h1, D.restrict_eq]
  exact (withDensity_absolutelyContinuous _ _).trans Measure.restrict_le_self.absolutelyContinuous


open FunctionalInequalities

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [FiniteDimensional ℝ E] in
theorem slope_comp_isometry {F : Type} [MetricSpace F] {g : F → E} (hg : Isometry g) (f : E → ℝ)
    (v : F) : Energy.LocalSlope.apply (f ∘ g) v ≤ Energy.LocalSlope.apply f (g v) := by
  unfold Energy.LocalSlope.apply
  refine iInf₂_mono fun r hr => ?_
  refine iSup₂_le fun w hw => ?_
  have hw' : dist (g w) (g v) < r := by rwa [hg.dist_eq]
  refine le_trans ?_ (le_iSup₂ (f := fun (y : E) (_ : dist y (g v) < r) =>
    ENNReal.ofReal (dist (f y) (f (g v)) / dist y (g v))) (g w) hw')
  simp [hg.dist_eq]

omit [InnerProductSpace ℝ E] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [FiniteDimensional ℝ E] in
theorem slope_clamp_le (f : E → ℝ) (M : ℝ) (x : E) :
    Energy.LocalSlope.apply (fun y => max (-M) (min M (f y))) x ≤ Energy.LocalSlope.apply f x := by
  unfold Energy.LocalSlope.apply
  refine iInf₂_mono fun r hr => ?_
  refine iSup₂_mono fun y hy => ?_
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ dist_nonneg
  rw [Real.dist_eq, Real.dist_eq]
  have hL : LipschitzWith 1 (fun t : ℝ => max (-M) (min M t)) :=
    (LipschitzWith.id.const_min M).const_max (-M)
  have := hL.dist_le_mul (f y) (f x)
  simpa [Real.dist_eq] using this

theorem measurableEmbedding_reconstruct (μ : ProbabilityMeasure E) :
    MeasurableEmbedding (Probability.reconstruct μ) :=
  (Probability.reconstruct μ).isometry.isClosedEmbedding.measurableEmbedding

theorem holds_ambient {μ : ProbabilityMeasure E} {C : ℝ≥0}
    (h : Poincare.LocalSlope.Holds (Probability.intrinsicMeasure μ) C)
    (f : E → ℝ) (hf : Energy.LocalSlope.Admissible μ f) :
    evariance f (μ : Measure E) ≤ C * Energy.LocalSlope.energy μ f := by
  set R := Probability.reconstruct μ with hR
  have hmp := Probability.measurePreserving_reconstruct μ
  have hme := measurableEmbedding_reconstruct μ
  set g := f ∘ R with hg
  have hlin : ∀ F : E → ℝ≥0∞, ∫⁻ v, F (R v) ∂(Probability.intrinsicMeasure μ : Measure _) =
      ∫⁻ x, F x ∂(μ : Measure E) := by
    intro F
    rw [← hme.lintegral_map, hmp.map_eq]
  have hint : ∫ v, g v ∂(Probability.intrinsicMeasure μ : Measure _) = ∫ x, f x ∂(μ : Measure E) := by
    rw [hg, ← hmp.map_eq, hme.integral_map]
    rfl
  have henergy : Energy.LocalSlope.energy (Probability.intrinsicMeasure μ) g ≤
      Energy.LocalSlope.energy μ f := by
    unfold Energy.LocalSlope.energy
    calc ∫⁻ v, Energy.LocalSlope.apply g v ^ 2 ∂(Probability.intrinsicMeasure μ : Measure _)
        ≤ ∫⁻ v, Energy.LocalSlope.apply f (R v) ^ 2 ∂(Probability.intrinsicMeasure μ : Measure _) := by
          apply lintegral_mono
          intro v
          exact pow_le_pow_left₀ (zero_le) (slope_comp_isometry R.isometry f v) 2
      _ = _ := hlin (fun x => Energy.LocalSlope.apply f x ^ 2)
  have hadm : Energy.LocalSlope.Admissible (Probability.intrinsicMeasure μ) g := by
    refine ⟨?_, ?_, ?_⟩
    · exact hf.locallyLipschitz.comp R.lipschitz.locallyLipschitz
    · exact hf.memLp_two.comp_measurePreserving hmp
    · exact ne_top_of_le_ne_top hf.finite_energy henergy
  have hvar : evariance g (Probability.intrinsicMeasure μ : Measure _) = evariance f (μ : Measure E) := by
    unfold evariance
    rw [hint]
    exact hlin (fun x => ‖f x - ∫ x, f x ∂(μ : Measure E)‖ₑ ^ 2)
  rw [← hvar]
  calc evariance g (Probability.intrinsicMeasure μ : Measure _)
      ≤ C * Energy.LocalSlope.energy (Probability.intrinsicMeasure μ) g := h g hadm
    _ ≤ C * Energy.LocalSlope.energy μ f := by gcongr


theorem ae_differentiableAt_of_locallyLipschitz {f : E → ℝ} (hf : LocallyLipschitz f)
    (m : Measure E) [m.IsAddHaarMeasure] : ∀ᵐ x ∂m, DifferentiableAt ℝ f x := by
  rw [ae_iff]
  apply measure_null_of_locally_null
  intro x _
  obtain ⟨K, U, hU, hLip⟩ := hf x
  refine ⟨{a | ¬ DifferentiableAt ℝ f a} ∩ interior U,
    inter_mem_nhdsWithin _ (interior_mem_nhds.2 hU), ?_⟩
  have := (hLip.mono interior_subset).ae_differentiableWithinAt_of_mem (μ := m)
  rw [ae_iff] at this
  refine measure_mono_null ?_ this
  intro y hy
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq] at hy ⊢
  intro hcon
  exact hy.1 ((hcon hy.2).differentiableAt (isOpen_interior.mem_nhds hy.2))

theorem slopeEnergy_eq_dirichlet {n : ℕ} {μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
    (hac : (μ : Measure (EuclideanSpace ℝ (Fin n))) ≪ volume)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : LocallyLipschitz f) :
    Energy.LocalSlope.energy μ f = SongZhangKLS.dirichletEnergy (μ : Measure _) f := by
  unfold Energy.LocalSlope.energy SongZhangKLS.dirichletEnergy
  apply lintegral_congr_ae
  filter_upwards [hac.ae_le (ae_differentiableAt_of_locallyLipschitz hf volume)] with x hx
  rw [Energy.LocalSlope.apply_eq_norm_gradient_readable f x hx, ofReal_norm]

omit [InnerProductSpace ℝ E] [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E] in
theorem lintegral_sq_sub_le (ν : Measure E) [IsProbabilityMeasure ν] (a : E → ℝ)
    (ha : Measurable a) :
    ∫⁻ x, ∫⁻ y, ‖a x - a y‖ₑ ^ 2 ∂ν ∂ν ≤ 4 * evariance a ν := by
  set m := ∫ x, a x ∂ν
  have hpt : ∀ x y, ‖a x - a y‖ₑ ^ 2 ≤ 2 * ‖a x - m‖ₑ ^ 2 + 2 * ‖a y - m‖ₑ ^ 2 := by
    intro x y
    have h : (a x - a y) ^ 2 ≤ 2 * (a x - m) ^ 2 + 2 * (a y - m) ^ 2 := by
      nlinarith [sq_nonneg (a x + a y - 2 * m)]
    have e : ∀ u : ℝ, ‖u‖ₑ ^ 2 = ENNReal.ofReal (u ^ 2) := by
      intro u
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
    rw [e, e, e]
    calc ENNReal.ofReal ((a x - a y) ^ 2) ≤ ENNReal.ofReal (2 * (a x - m) ^ 2 + 2 * (a y - m) ^ 2) :=
          ENNReal.ofReal_le_ofReal h
      _ = 2 * ENNReal.ofReal ((a x - m) ^ 2) + 2 * ENNReal.ofReal ((a y - m) ^ 2) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_mul (by norm_num)]
          simp
  have hmeas1 : Measurable fun x => ‖a x - m‖ₑ ^ 2 := by fun_prop
  calc ∫⁻ x, ∫⁻ y, ‖a x - a y‖ₑ ^ 2 ∂ν ∂ν
      ≤ ∫⁻ x, ∫⁻ y, (2 * ‖a x - m‖ₑ ^ 2 + 2 * ‖a y - m‖ₑ ^ 2) ∂ν ∂ν := by
        gcongr with x y; exact hpt x y
    _ = ∫⁻ x, (2 * ‖a x - m‖ₑ ^ 2 + 2 * evariance a ν) ∂ν := by
        apply lintegral_congr; intro x
        rw [lintegral_add_left (by fun_prop), lintegral_const, lintegral_const_mul _ hmeas1]
        simp [evariance, m]
    _ = 4 * evariance a ν := by
        rw [lintegral_add_left (by fun_prop), lintegral_const_mul _ hmeas1, lintegral_const]
        simp [evariance, m]
        ring

/-- clamped squared difference -/
noncomputable def clampF (f : E → ℝ) (M : ℕ) (x y : E) : ℝ≥0∞ :=
  ‖max (-(M : ℝ)) (min (M : ℝ) (f x)) - max (-(M : ℝ)) (min (M : ℝ) (f y))‖ₑ ^ 2

omit [InnerProductSpace ℝ E] [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E] in
theorem measurable_clampF {f : E → ℝ} (hf : Measurable f) (M : ℕ) :
    Measurable (Function.uncurry (clampF f M)) := by
  unfold clampF Function.uncurry
  fun_prop

omit [InnerProductSpace ℝ E] [CompleteSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E] in
set_option maxHeartbeats 2000000 in
theorem memLp_of_clamp_evariance_le (ν : Measure E) [IsProbabilityMeasure ν] (f : E → ℝ)
    (hf : Measurable f) (B : ℝ≥0∞) (hB : B ≠ ⊤)
    (h : ∀ M : ℕ, evariance (fun y => max (-(M : ℝ)) (min (M : ℝ) (f y))) ν ≤ B) :
    MemLp f 2 ν := by
  let F : ℕ → E → E → ℝ≥0∞ := clampF f
  have hFmeas : ∀ M, Measurable (Function.uncurry (F M)) := measurable_clampF hf
  have hFy : ∀ M x, Measurable (fun y => F M x y) := fun M x =>
    (hFmeas M).comp (measurable_prodMk_left (m := inferInstance))
  have hclamp : ∀ (M : ℕ) (t : ℝ), |t| ≤ M → max (-(M : ℝ)) (min (M : ℝ) t) = t := by
    intro M t ht
    have := abs_le.1 ht
    rw [min_eq_right this.2, max_eq_right this.1]
  have hev : ∀ x y, (fun M => F M x y) =ᶠ[atTop] fun _ => ‖f x - f y‖ₑ ^ 2 := by
    intro x y
    filter_upwards [eventually_ge_atTop (⌈max |f x| |f y|⌉₊)] with M hM
    have hM' : max |f x| |f y| ≤ (M : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hM)
    simp only [F, clampF]
    rw [hclamp M (f x) ((le_max_left _ _).trans hM'), hclamp M (f y) ((le_max_right _ _).trans hM')]
  have hlim : ∀ x y, liminf (fun M => F M x y) atTop = ‖f x - f y‖ₑ ^ 2 := by
    intro x y
    exact (tendsto_const_nhds.congr' (hev x y).symm).liminf_eq
  have hbound : ∀ M, ∫⁻ x, ∫⁻ y, F M x y ∂ν ∂ν ≤ 4 * B := by
    intro M
    calc ∫⁻ x, ∫⁻ y, F M x y ∂ν ∂ν ≤ 4 * evariance (fun y => max (-(M : ℝ)) (min (M : ℝ) (f y))) ν :=
          lintegral_sq_sub_le ν _ (by fun_prop)
      _ ≤ 4 * B := by gcongr; exact h M
  have hinner : ∀ M, Measurable fun x => ∫⁻ y, F M x y ∂ν := fun M =>
    (hFmeas M).lintegral_prod_right'
  have hG : ∫⁻ x, ∫⁻ y, ‖f x - f y‖ₑ ^ 2 ∂ν ∂ν ≤ 4 * B := by
    calc ∫⁻ x, ∫⁻ y, ‖f x - f y‖ₑ ^ 2 ∂ν ∂ν
        = ∫⁻ x, ∫⁻ y, liminf (fun M => F M x y) atTop ∂ν ∂ν := by simp_rw [hlim]
      _ ≤ ∫⁻ x, liminf (fun M => ∫⁻ y, F M x y ∂ν) atTop ∂ν := by
          gcongr with x
          exact lintegral_liminf_le (fun M => hFy M x)
      _ ≤ liminf (fun M => ∫⁻ x, ∫⁻ y, F M x y ∂ν ∂ν) atTop := lintegral_liminf_le hinner
      _ ≤ liminf (fun _ : ℕ => 4 * B) atTop := liminf_le_liminf (Eventually.of_forall hbound)
      _ = 4 * B := liminf_const _
  have hfin : ∫⁻ x, ∫⁻ y, ‖f x - f y‖ₑ ^ 2 ∂ν ∂ν < ⊤ :=
    lt_of_le_of_lt hG (ENNReal.mul_lt_top (by norm_num) hB.lt_top)
  obtain ⟨x0, hx0⟩ : ∃ x0, ∫⁻ y, ‖f x0 - f y‖ₑ ^ 2 ∂ν < ⊤ := by
    by_contra hcon
    push_neg at hcon
    have : ∫⁻ x, ∫⁻ y, ‖f x - f y‖ₑ ^ 2 ∂ν ∂ν = ⊤ := by
      have : (fun x => ∫⁻ y, ‖f x - f y‖ₑ ^ 2 ∂ν) = fun _ => ⊤ := by
        funext x; exact top_le_iff.1 (hcon x)
      rw [this, lintegral_const]; simp
    exact absurd hfin (by rw [this]; exact lt_irrefl _)
  have hmem : MemLp (fun y => f x0 - f y) 2 ν := by
    rw [memLp_two_iff_integrable_sq (by fun_prop)]
    refine ⟨by fun_prop, ?_⟩
    unfold HasFiniteIntegral
    simpa [enorm_pow] using hx0
  have : f = fun y => f x0 - (f x0 - f y) := by funext y; ring
  rw [this]
  exact (memLp_const _).sub hmem


theorem holds_mono {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [FiniteDimensional ℝ V]
    {ν : ProbabilityMeasure V} {C C' : ℝ≥0} (h : Poincare.LocalSlope.Holds ν C) (hC : C ≤ C') :
    Poincare.LocalSlope.Holds ν C' := by
  intro f hf
  calc evariance f (ν : Measure V) ≤ C * Energy.LocalSlope.energy ν f := h f hf
    _ ≤ C' * Energy.LocalSlope.energy ν f := by gcongr

theorem partA : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))),
    KLS.LogConcave μ → KLS.Isotropic μ →
    ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, LocallyLipschitz f →
      SongZhangKLS.dirichletEnergy (μ : Measure (EuclideanSpace ℝ (Fin n))) f < ⊤ →
      MemLp f 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
      evariance f (μ : Measure (EuclideanSpace ℝ (Fin n))) ≤
        ENNReal.ofReal C * SongZhangKLS.dirichletEnergy (μ : Measure (EuclideanSpace ℝ (Fin n))) f := by
  obtain ⟨K, hKpos, hK⟩ := KLS.BKL.Localization.exists_isotropicBound_readable.{0}
  refine ⟨(K : ℝ) + 1, by positivity, ?_⟩
  intro n μ hlc hiso f hf hE
  have hconst := hK (EuclideanSpace ℝ (Fin n)) μ hlc hiso
  have hholds : Poincare.LocalSlope.Holds (Probability.intrinsicMeasure μ) (K + 1) := by
    have hlt : Poincare.LocalSlope.Intrinsic.constant μ < ((K + 1 : ℝ≥0) : ℝ≥0∞) :=
      lt_of_le_of_lt hconst (by exact_mod_cast (lt_add_one K))
    unfold Poincare.LocalSlope.Intrinsic.constant at hlt
    obtain ⟨⟨C, hC⟩, hClt⟩ := iInf_lt_iff.1 hlt
    exact holds_mono hC (by exact_mod_cast hClt.le)
  have hac := absolutelyContinuous (volume : Measure (EuclideanSpace ℝ (Fin n))) hlc hiso
  have hCeq : ENNReal.ofReal ((K : ℝ) + 1) = ((K + 1 : ℝ≥0) : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_coe_nnreal]; simp
  rw [hCeq]
  have hfm : Measurable f := hf.continuous.measurable
  -- bound for admissible functions
  have key : ∀ g : EuclideanSpace ℝ (Fin n) → ℝ, LocallyLipschitz g →
      MemLp g 2 (μ : Measure _) → Energy.LocalSlope.energy μ g ≠ ⊤ →
      evariance g (μ : Measure _) ≤ ((K + 1 : ℝ≥0) : ℝ≥0∞) * Energy.LocalSlope.energy μ g :=
    fun g hg h2 h3 => holds_ambient hholds g ⟨hg, h2, h3⟩
  have hEs : Energy.LocalSlope.energy μ f = SongZhangKLS.dirichletEnergy (μ : Measure _) f :=
    slopeEnergy_eq_dirichlet hac hf
  have hclampE : ∀ M : ℕ, Energy.LocalSlope.energy μ (fun y => max (-(M : ℝ)) (min (M : ℝ) (f y))) ≤
      Energy.LocalSlope.energy μ f := by
    intro M
    unfold Energy.LocalSlope.energy
    gcongr with x
    exact slope_clamp_le f M x
  have hmem : MemLp f 2 (μ : Measure _) := by
    apply memLp_of_clamp_evariance_le (μ : Measure _) f hfm
      (((K + 1 : ℝ≥0) : ℝ≥0∞) * SongZhangKLS.dirichletEnergy (μ : Measure _) f)
      (ENNReal.mul_ne_top (by simp) hE.ne)
    intro M
    set g := fun y => max (-(M : ℝ)) (min (M : ℝ) (f y))
    have hg : LocallyLipschitz g := (hf.const_min (M : ℝ)).const_max (-(M : ℝ))
    have hgb : ∀ y, ‖g y‖ ≤ M := by
      intro y
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · exact le_max_left _ _
      · exact max_le (by have := (Nat.cast_nonneg M : (0:ℝ) ≤ M); linarith) (min_le_left _ _)
    have hg2 : MemLp g 2 (μ : Measure _) :=
      MemLp.of_bound (by fun_prop) (M : ℝ) (Eventually.of_forall hgb)
    calc evariance g (μ : Measure _) ≤ ((K + 1 : ℝ≥0) : ℝ≥0∞) * Energy.LocalSlope.energy μ g :=
          key g hg hg2 (ne_top_of_le_ne_top (hEs ▸ hE.ne) (hclampE M))
      _ ≤ ((K + 1 : ℝ≥0) : ℝ≥0∞) * SongZhangKLS.dirichletEnergy (μ : Measure _) f := by
          gcongr; rw [← hEs]; exact hclampE M
  refine ⟨hmem, ?_⟩
  rw [← hEs]
  exact key f hf hmem (hEs ▸ hE.ne)

end SZPartA


-- ===== from Solutions/KB/Gauss.lean =====

open MeasureTheory ProbabilityTheory Complex
open FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
open scoped RealInnerProductSpace

namespace KB
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem charFun_gaussianLaw {t : ℝ} (ht : 0 < t) (u : V) :
    charFun (gaussianLaw (V := V) t) u = cexp (-(‖u‖ ^ 2 / (4 * t) : ℝ)) := by
  rw [charFun_apply, gaussianLaw, integral_withDensity_eq_integral_toReal_smul
    (normalizedKernel_measurable t).ennreal_ofReal (Filter.Eventually.of_forall fun _ => by simp)]
  have h1 : ∀ x : V, (ENNReal.ofReal (normalizedKernel t x)).toReal • cexp (⟪x, u⟫ * I) =
      ((mass (V := V) t)⁻¹ : ℂ) * cexp (-(t : ℂ) * ‖x‖ ^ 2 + I * ⟪u, x⟫) := by
    intro x
    rw [ENNReal.toReal_ofReal (normalizedKernel_pos ht x).le, normalizedKernel, kernel,
      Complex.real_smul, div_eq_inv_mul, Complex.ofReal_mul, mul_assoc, Complex.ofReal_exp,
      ← Complex.exp_add, real_inner_comm]
    push_cast
    ring_nf
  simp_rw [h1]
  rw [integral_const_mul, GaussianFourier.integral_cexp_neg_mul_sq_norm_add (by simpa using ht)]
  have hm : ((mass (V := V) t) : ℂ) = (Real.pi / t : ℂ) ^ (Module.finrank ℝ V / 2 : ℂ) := by
    rw [mass, Complex.ofReal_cpow (by positivity)]
    push_cast; ring_nf
  rw [← hm, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast (mass_pos (V := V) ht).ne'), one_mul]
  congr 1
  push_cast
  rw [I_sq]
  ring

theorem charFun_gaussianLaw' {t : ℝ} (ht : 0 < t) (u : V) :
    charFun (gaussianLaw (V := V) t) u = cexp (-(‖u‖ ^ 2 / (4 * t) : ℝ)) :=
  charFun_gaussianLaw ht u

instance gaussianLaw_isProb {t : ℝ} [Fact (0 < t)] : IsProbabilityMeasure (gaussianLaw (V := V) t) :=
  gaussianLaw_probability Fact.out

/-- the rotation map on pairs -/
noncomputable def rotCLM (c s : ℝ) : V × V →L[ℝ] V × V :=
  ((c • ContinuousLinearMap.fst ℝ V V) + (s • ContinuousLinearMap.snd ℝ V V)).prod
    ((-s) • ContinuousLinearMap.fst ℝ V V + c • ContinuousLinearMap.snd ℝ V V)

theorem rotCLM_apply (c s : ℝ) (p : V × V) :
    rotCLM c s p = (c • p.1 + s • p.2, (-s) • p.1 + c • p.2) := rfl

variable [CompleteSpace V] [SecondCountableTopology V]

theorem charFunDual_gaussianLaw_toDual {t : ℝ} (ht : 0 < t) (a : V) :
    charFunDual (gaussianLaw (V := V) t) (InnerProductSpace.toDual ℝ V a) =
      cexp (-(‖a‖ ^ 2 / (4 * t) : ℝ)) := by
  rw [← charFun_toDual_symm_eq_charFunDual]
  simp [charFun_gaussianLaw ht]

theorem map_rot_gaussian {t : ℝ} (ht : 0 < t) (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    ((gaussianLaw (V := V) t).prod (gaussianLaw (V := V) t)).map (rotCLM c s) =
      (gaussianLaw (V := V) t).prod (gaussianLaw (V := V) t) := by
  haveI : Fact (0 < t) := ⟨ht⟩
  haveI : IsProbabilityMeasure (((gaussianLaw (V := V) t).prod (gaussianLaw (V := V) t)).map
    (rotCLM c s)) := Measure.isProbabilityMeasure_map (by fun_prop)
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_map, charFunDual_prod, charFunDual_prod]
  set a := (InnerProductSpace.toDual ℝ V).symm (L.comp (.inl ℝ V V))
  set b := (InnerProductSpace.toDual ℝ V).symm (L.comp (.inr ℝ V V))
  have ha : L.comp (.inl ℝ V V) = InnerProductSpace.toDual ℝ V a := by simp [a]
  have hb : L.comp (.inr ℝ V V) = InnerProductSpace.toDual ℝ V b := by simp [b]
  have hL : ∀ p : V × V, L p = ⟪a, p.1⟫ + ⟪b, p.2⟫ := by
    intro p
    have := L.comp_inl_add_comp_inr
    conv_lhs => rw [← this]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_comp',
      Function.comp_apply]
    rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply, ha, hb]
    simp
  have h1 : (L.comp (rotCLM c s)).comp (.inl ℝ V V) =
      InnerProductSpace.toDual ℝ V (c • a - s • b) := by
    ext w
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.inl_apply,
      rotCLM_apply, hL, InnerProductSpace.toDual_apply_apply]
    simp [inner_smul_right, inner_sub_left, inner_smul_left]
    ring
  have h2 : (L.comp (rotCLM c s)).comp (.inr ℝ V V) =
      InnerProductSpace.toDual ℝ V (s • a + c • b) := by
    ext w
    simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.inr_apply,
      rotCLM_apply, hL, InnerProductSpace.toDual_apply_apply]
    simp [inner_smul_right, inner_add_left, inner_smul_left]
  rw [h1, h2, ha, hb, charFunDual_gaussianLaw_toDual ht, charFunDual_gaussianLaw_toDual ht,
    charFunDual_gaussianLaw_toDual ht, charFunDual_gaussianLaw_toDual ht, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  have e1 : ‖c • a - s • b‖ ^ 2 + ‖s • a + c • b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_add_sq_real, norm_smul, norm_smul, norm_smul, norm_smul,
      inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right]
    simp only [Real.norm_eq_abs, mul_pow, sq_abs, conj_trivial]
    nlinarith [hcs]
  push_cast
  rw [show (-(↑‖c • a - s • b‖ ^ 2 / (4 * (t:ℂ))) + -(↑‖s • a + c • b‖ ^ 2 / (4 * (t:ℂ)))) =
    -(((‖c • a - s • b‖ ^ 2 + ‖s • a + c • b‖ ^ 2 : ℝ) : ℂ) / (4 * t)) by push_cast; ring, e1]
  push_cast; ring

end KB


-- ===== from Solutions/KB/Heat.lean =====

open MeasureTheory ProbabilityTheory
open FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
open scoped RealInnerProductSpace

namespace KB
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- Gaussian smoothing of a function, kernel form. -/
noncomputable def heat (t : ℝ) (h : V → ℝ) (x : V) : ℝ :=
  ∫ y, h y * normalizedKernel t (x - y)

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem normalizedKernel_sub_le {t : ℝ} (ht : 0 < t) (x x0 y : V) (hx : ‖x - x0‖ < 1) :
    normalizedKernel t (x - y) ≤
      Real.exp t * Real.exp (-(t / 2) * ‖x0 - y‖ ^ 2) / mass (V := V) t := by
  unfold normalizedKernel kernel
  apply div_le_div_of_nonneg_right _ (mass_pos ht).le
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  have h1 : ‖x0 - y‖ ≤ ‖x - y‖ + ‖x - x0‖ := by
    calc ‖x0 - y‖ = ‖(x - y) - (x - x0)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have h2 : ‖x0 - y‖ ^ 2 ≤ 2 * ‖x - y‖ ^ 2 + 2 * ‖x - x0‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖x - y‖ - ‖x - x0‖)]
  have h3 : ‖x - x0‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg (x - x0)]
  nlinarith

theorem integrable_poly_kernel {t : ℝ} (ht : 0 < t) (x0 : V) :
    Integrable (fun y : V => (‖x0 - y‖ + 1) * Real.exp (-(t / 2) * ‖x0 - y‖ ^ 2)) := by
  obtain ⟨B, hB⟩ := one_add_pow_mul_exp_neg_sq_bounded (t / 4) (by positivity) 1
  have hk : Integrable (fun y : V => B * kernel (t / 4) (x0 - y)) :=
    ((integrable_kernel (V := V) (by positivity : 0 < t / 4)).comp_sub_left x0).const_mul B
  refine hk.mono' (by fun_prop) (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  have := hB ‖x0 - y‖ (norm_nonneg _)
  unfold kernel
  have e : Real.exp (-(t / 2) * ‖x0 - y‖ ^ 2) =
      Real.exp (-(t / 4) * ‖x0 - y‖ ^ 2) * Real.exp (-(t / 4) * ‖x0 - y‖ ^ 2) := by
    rw [← Real.exp_add]; ring_nf
  rw [e, ← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  simpa [add_comm] using this

/-- the derivative of the kernel in the first variable -/
theorem hasFDerivAt_normalizedKernel_sub (t : ℝ) (x y : V) :
    HasFDerivAt (fun x => normalizedKernel t (x - y))
      ((normalizedKernel t (x - y) * (-2 * t)) • innerSL ℝ (x - y)) x := by
  have h1 : HasFDerivAt (fun x : V => ‖x - y‖ ^ 2) ((2 : ℝ) • innerSL ℝ (x - y)) x := by
    have := ((hasFDerivAt_id x).sub_const y).norm_sq
    refine this.congr_fderiv ?_
    ext v
    simp [innerSL_apply_apply, two_smul]
  have h2 := (((h1.const_mul (-t)).exp).mul_const (mass (V := V) t)⁻¹)
  have h3 : (fun x => normalizedKernel t (x - y)) =
      fun x => Real.exp (-t * ‖x - y‖ ^ 2) * (mass (V := V) t)⁻¹ := by
    funext x; simp [normalizedKernel, kernel, div_eq_mul_inv]
  rw [h3]
  refine h2.congr_fderiv ?_
  ext v
  simp [normalizedKernel, kernel, div_eq_mul_inv, innerSL_apply_apply]
  ring

/-- Gaussian smoothing of a bounded measurable function is differentiable. -/
theorem hasFDerivAt_heat {t : ℝ} (ht : 0 < t) {h : V → ℝ} (hm : Measurable h) {M : ℝ}
    (hM : ∀ y, |h y| ≤ M) (x0 : V) :
    HasFDerivAt (heat t h)
      (∫ y, (h y * (normalizedKernel t (x0 - y) * (-2 * t))) • innerSL ℝ (x0 - y)) x0 := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hkm : Measurable (normalizedKernel (V := V) t) := normalizedKernel_measurable t
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := volume) (F := fun x y => h y * normalizedKernel t (x - y))
    (F' := fun x y => (h y * (normalizedKernel t (x - y) * (-2 * t))) • innerSL ℝ (x - y))
    (bound := fun y => M * (2 * t) * (Real.exp t / mass (V := V) t) *
      ((‖x0 - y‖ + 1) * Real.exp (-(t / 2) * ‖x0 - y‖ ^ 2)))
    (Metric.ball_mem_nhds x0 one_pos) ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x => by fun_prop
  · refine Integrable.mono' (((integrable_normalizedKernel (V := V) ht).comp_sub_left x0).const_mul M)
      (by fun_prop) (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (normalizedKernel_pos ht _)]
    exact mul_le_mul_of_nonneg_right (hM y) (normalizedKernel_pos ht _).le
  · fun_prop
  · refine Filter.Eventually.of_forall fun y x hx => ?_
    rw [Metric.mem_ball, dist_eq_norm] at hx
    have hk := normalizedKernel_sub_le ht x x0 y hx
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (normalizedKernel_pos ht _),
      abs_of_neg (by linarith : -2 * t < 0), innerSL_apply_norm]
    have hxy : ‖x - y‖ ≤ ‖x0 - y‖ + 1 := by
      calc ‖x - y‖ = ‖(x0 - y) + (x - x0)‖ := by congr 1; abel
        _ ≤ ‖x0 - y‖ + ‖x - x0‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    have hkpos := (normalizedKernel_pos ht (x - y)).le
    rw [show -(-2 * t) = 2 * t by ring]
    have hK0 : 0 ≤ Real.exp t * Real.exp (-(t / 2) * ‖x0 - y‖ ^ 2) / mass (V := V) t :=
      div_nonneg (by positivity) (mass_pos ht).le
    calc |h y| * (normalizedKernel t (x - y) * (2 * t)) * ‖x - y‖
        ≤ M * ((Real.exp t * Real.exp (-(t / 2) * ‖x0 - y‖ ^ 2) / mass (V := V) t) * (2 * t)) *
            (‖x0 - y‖ + 1) := by
          apply mul_le_mul _ hxy (norm_nonneg _) (by positivity)
          apply mul_le_mul (hM y) _ (by positivity) hM0
          exact mul_le_mul_of_nonneg_right hk (by linarith)
      _ = _ := by ring
  · exact (integrable_poly_kernel ht x0).const_mul _
  · refine Filter.Eventually.of_forall fun y x _ => ?_
    have := (hasFDerivAt_normalizedKernel_sub t x y).const_mul (h y)
    refine this.congr_fderiv ?_
    rw [smul_smul]


theorem integral_kernel_eq {t : ℝ} (ht : 0 < t) (g : V → ℝ) (x : V) :
    ∫ y, g y * normalizedKernel t (x - y) = ∫ z, g (x + z) ∂(gaussianLaw t) := by
  rw [gaussianLaw, integral_withDensity_eq_integral_toReal_smul
    (normalizedKernel_measurable t).ennreal_ofReal (Filter.Eventually.of_forall fun _ => by simp)]
  have e := integral_add_left_eq_self (μ := (volume : Measure V))
    (f := fun y => g y * normalizedKernel t (x - y)) x
  rw [← e]
  congr 1
  funext z
  rw [show x - (x + z) = -z by abel,
    show normalizedKernel t (-z) = normalizedKernel t z by simp [normalizedKernel, kernel, norm_neg],
    ENNReal.toReal_ofReal (normalizedKernel_pos ht z).le, smul_eq_mul, mul_comm]

theorem heat_eq {t : ℝ} (ht : 0 < t) (h : V → ℝ) (x : V) :
    heat t h x = ∫ z, h (x + z) ∂(gaussianLaw t) :=
  integral_kernel_eq ht h x

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem abs_inner_sq_le_exp (v y : V) : ⟪y, v⟫ ^ 2 ≤ ‖v‖ ^ 2 * (2 * Real.exp ‖y‖) := by
  have h1 : ⟪y, v⟫ ^ 2 ≤ (‖y‖ * ‖v‖) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm y v) 2
  have h2 : ‖y‖ ^ 2 ≤ 2 * Real.exp ‖y‖ := by
    nlinarith [Real.quadratic_le_exp_of_nonneg (norm_nonneg y), norm_nonneg y]
  nlinarith [sq_nonneg ‖v‖]


section GaussMoments
variable {t : ℝ}

theorem memLp_inner_gaussian (ht : 0 < t) (v : V) :
    MemLp (fun y : V => ⟪v, y⟫) 2 (gaussianLaw t) := by
  haveI := gaussianLaw_probability (V := V) ht
  have hexp := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_exp_norm_integrable_readable
    (E := V) ht
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  refine (hexp.const_mul (‖v‖ ^ 2 * 2)).mono' (by fun_prop) (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _), real_inner_comm]
  have := abs_inner_sq_le_exp v y
  linarith

theorem integrable_id_gaussian (ht : 0 < t) : Integrable (fun y : V => y) (gaussianLaw t) := by
  haveI := gaussianLaw_probability (V := V) ht
  have hexp := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_exp_norm_integrable_readable
    (E := V) ht
  refine hexp.mono' (by fun_prop) (Filter.Eventually.of_forall fun y => ?_)
  have := Real.add_one_le_exp ‖y‖
  linarith

theorem integral_inner_gaussian (ht : 0 < t) (v : V) : ∫ y, ⟪v, y⟫ ∂(gaussianLaw t) = 0 := by
  rw [integral_inner (integrable_id_gaussian ht) v,
    FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_mean_zero_readable ht]
  simp

end GaussMoments

/-- the derivative of `heat` -/
noncomputable def heatD (t : ℝ) (h : V → ℝ) (x0 : V) : V →L[ℝ] ℝ :=
  ∫ y, (h y * (normalizedKernel t (x0 - y) * (-2 * t))) • innerSL ℝ (x0 - y)

theorem integrable_heatD {t : ℝ} (ht : 0 < t) {h : V → ℝ} (hm : Measurable h) {M : ℝ}
    (hM : ∀ y, |h y| ≤ M) (x0 : V) :
    Integrable (fun y => (h y * (normalizedKernel t (x0 - y) * (-2 * t))) • innerSL ℝ (x0 - y)) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hkm : Measurable (normalizedKernel (V := V) t) := normalizedKernel_measurable t
  have hmeas : Measurable (fun y => (h y * (normalizedKernel t (x0 - y) * (-2 * t))) •
      innerSL ℝ (x0 - y)) := by
    exact (hm.mul ((hkm.comp (measurable_const.sub measurable_id)).mul_const _)).smul
      ((innerSL ℝ).continuous.measurable.comp (measurable_const.sub measurable_id))
  refine ((integrable_poly_kernel ht x0).const_mul (M * (2 * t) * (Real.exp t / mass (V := V) t))).mono'
    hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
  have hk := normalizedKernel_sub_le ht x0 x0 y (by simp)
  rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (normalizedKernel_pos ht _),
    abs_of_neg (by linarith : -2 * t < 0), innerSL_apply_norm, show -(-2 * t) = 2 * t by ring]
  have hK0 : 0 ≤ Real.exp t * Real.exp (-(t / 2) * ‖x0 - y‖ ^ 2) / mass (V := V) t :=
    div_nonneg (by positivity) (mass_pos ht).le
  calc |h y| * (normalizedKernel t (x0 - y) * (2 * t)) * ‖x0 - y‖
      ≤ M * ((Real.exp t * Real.exp (-(t / 2) * ‖x0 - y‖ ^ 2) / mass (V := V) t) * (2 * t)) *
          (‖x0 - y‖ + 1) := by
        apply mul_le_mul _ (by linarith) (norm_nonneg _)
          (mul_nonneg hM0 (mul_nonneg hK0 (by linarith)))
        apply mul_le_mul (hM y) _ (mul_nonneg (normalizedKernel_pos ht _).le (by linarith)) hM0
        exact mul_le_mul_of_nonneg_right hk (by linarith)
    _ = _ := by ring

theorem heatD_apply {t : ℝ} (ht : 0 < t) {h : V → ℝ} (hm : Measurable h) {M : ℝ}
    (hM : ∀ y, |h y| ≤ M) (x0 v : V) :
    heatD t h x0 v = 2 * t * ∫ z, h (x0 + z) * ⟪v, z⟫ ∂(gaussianLaw t) := by
  unfold heatD
  rw [ContinuousLinearMap.integral_apply (integrable_heatD ht hm hM x0)]
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
  have e : ∀ y, h y * (normalizedKernel t (x0 - y) * (-2 * t)) * ⟪x0 - y, v⟫ =
      (h y * (-2 * t) * ⟪x0 - y, v⟫) * normalizedKernel t (x0 - y) := by intro y; ring
  simp_rw [e]
  rw [integral_kernel_eq ht (fun y => h y * (-2 * t) * ⟪x0 - y, v⟫) x0, ← integral_const_mul]
  congr 1
  funext z
  rw [show x0 - (x0 + z) = -z by abel, inner_neg_left, real_inner_comm]
  ring

theorem hasFDerivAt_heat' {t : ℝ} (ht : 0 < t) {h : V → ℝ} (hm : Measurable h) {M : ℝ}
    (hM : ∀ y, |h y| ≤ M) (x0 : V) : HasFDerivAt (heat t h) (heatD t h x0) x0 :=
  hasFDerivAt_heat ht hm hM x0

theorem heat_abs_le {t : ℝ} (ht : 0 < t) {h : V → ℝ} {M : ℝ} (hM : ∀ y, |h y| ≤ M) (x : V) :
    |heat t h x| ≤ M := by
  haveI := gaussianLaw_probability (V := V) ht
  rw [heat_eq ht]
  calc |∫ z, h (x + z) ∂(gaussianLaw t)| ≤ ∫ z, |h (x + z)| ∂(gaussianLaw t) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _z, M ∂(gaussianLaw t) := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
          (integrable_const M) (Filter.Eventually.of_forall fun z => hM (x + z))
    _ = M := by simp

theorem norm_fderiv_heat_sq_le {t : ℝ} (ht : 0 < t) {h : V → ℝ} (hm : Measurable h) {M : ℝ}
    (hM : ∀ y, |h y| ≤ M) (x : V) :
    ‖fderiv ℝ (heat t h) x‖ ^ 2 ≤ 2 * t * (heat t (fun y => h y ^ 2) x - heat t h x ^ 2) := by
  haveI := gaussianLaw_probability (V := V) ht
  rw [(hasFDerivAt_heat' ht hm hM x).fderiv]
  set X : V → ℝ := fun z => h (x + z)
  have hXm : MemLp X 2 (gaussianLaw t) :=
    MemLp.of_bound (by fun_prop) M (Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs]; exact hM _)
  have hvarX : variance X (gaussianLaw t) = heat t (fun y => h y ^ 2) x - heat t h x ^ 2 := by
    rw [variance_eq_sub hXm, heat_eq ht, heat_eq ht]
    rfl
  have hV0 : 0 ≤ variance X (gaussianLaw t) := variance_nonneg _ _
  set Var := heat t (fun y => h y ^ 2) x - heat t h x ^ 2
  have key : ∀ v, |heatD t h x v| ≤ Real.sqrt (2 * t * Var) * ‖v‖ := by
    intro v
    have hY := memLp_inner_gaussian ht v
    have hcov : ∫ z, h (x + z) * ⟪v, z⟫ ∂(gaussianLaw t) = covariance X (fun y => ⟪v, y⟫) (gaussianLaw t) := by
      rw [covariance_eq_sub hXm hY, integral_inner_gaussian ht v]
      simp [X]
    have hcs := FunctionalInequalities.Probability.covariance_sq_le_variance_mul_variance_readable hXm hY
    rw [FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_variance_readable ht v] at hcs
    rw [heatD_apply ht hm hM, hcov]
    rw [show Real.sqrt (2 * t * Var) * ‖v‖ = Real.sqrt ((2 * t * Var) * ‖v‖ ^ 2) by
      rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]]
    apply Real.abs_le_sqrt
    rw [mul_pow]
    have : (2 * t) ^ 2 * covariance X (fun y => ⟪v, y⟫) (gaussianLaw t) ^ 2 ≤
        (2 * t) ^ 2 * (variance X (gaussianLaw t) * (‖v‖ ^ 2 / (2 * t))) :=
      mul_le_mul_of_nonneg_left hcs (by positivity)
    rw [hvarX] at this
    calc (2 * t) ^ 2 * covariance X (fun y => ⟪v, y⟫) (gaussianLaw t) ^ 2
        ≤ (2 * t) ^ 2 * (Var * (‖v‖ ^ 2 / (2 * t))) := this
      _ = 2 * t * Var * ‖v‖ ^ 2 := by field_simp
  have hle : ‖heatD t h x‖ ≤ Real.sqrt (2 * t * Var) :=
    ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun v => by
      rw [Real.norm_eq_abs]; exact key v
  calc ‖heatD t h x‖ ^ 2 ≤ Real.sqrt (2 * t * Var) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = 2 * t * Var := Real.sq_sqrt (mul_nonneg (by linarith) (hvarX ▸ hV0))


theorem sq_integral_le_integral_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {g : Ω → ℝ} (hg : MemLp g 2 μ) :
    (∫ ω, g ω ∂μ) ^ 2 ≤ ∫ ω, g ω ^ 2 ∂μ := by
  have h1 := variance_nonneg g μ
  rw [variance_eq_sub hg] at h1
  simp only [Pi.pow_apply] at h1
  linarith

/-- Gaussian smoothing commutes with differentiation for differentiable `h` with bounded
derivative. -/
theorem hasFDerivAt_heat_of_differentiable {t : ℝ} (ht : 0 < t) {h : V → ℝ}
    (hd : Differentiable ℝ h) {L M : ℝ} (hL : ∀ y, ‖fderiv ℝ h y‖ ≤ L) (hM : ∀ y, |h y| ≤ M)
    (x0 : V) :
    HasFDerivAt (heat t h) (∫ z, fderiv ℝ h (x0 + z) ∂(gaussianLaw t)) x0 := by
  haveI := gaussianLaw_probability (V := V) ht
  have heq : heat t h = fun x => ∫ z, h (x + z) ∂(gaussianLaw t) := by
    funext x; exact heat_eq ht h x
  rw [heq]
  have hc : Continuous h := hd.continuous
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := gaussianLaw t)
    (F := fun x z => h (x + z)) (F' := fun x z => fderiv ℝ h (x + z)) (bound := fun _ => L)
    (Metric.ball_mem_nhds x0 one_pos) ?_ ?_ ?_ ?_ (integrable_const L) ?_
  · exact Filter.Eventually.of_forall fun x =>
      (hc.comp (continuous_const.add continuous_id) : Continuous fun z => h (x + z)).aestronglyMeasurable
  · have hcz : Continuous (fun z => h (x0 + z)) := hc.comp (continuous_const.add continuous_id)
    exact (MemLp.of_bound hcz.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hM _)).integrable one_le_two
  · exact ((measurable_fderiv ℝ h).comp (measurable_const.add measurable_id)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z x _ => hL _
  · refine Filter.Eventually.of_forall fun z x _ => ?_
    exact (hd (x + z)).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const z) |>.congr_fderiv (by simp)

theorem norm_fderiv_heat_sq_le_of_differentiable {t : ℝ} (ht : 0 < t) {h : V → ℝ}
    (hd : Differentiable ℝ h) {L M : ℝ} (hL : ∀ y, ‖fderiv ℝ h y‖ ≤ L) (hM : ∀ y, |h y| ≤ M)
    (x : V) :
    ‖fderiv ℝ (heat t h) x‖ ^ 2 ≤ heat t (fun y => ‖fderiv ℝ h y‖ ^ 2) x := by
  haveI := gaussianLaw_probability (V := V) ht
  rw [(hasFDerivAt_heat_of_differentiable ht hd hL hM x).fderiv, heat_eq ht]
  have hL0 : 0 ≤ L := le_trans (norm_nonneg _) (hL 0)
  have hmeas : Measurable fun z => ‖fderiv ℝ h (x + z)‖ :=
    ((measurable_fderiv ℝ h).comp (measurable_const.add measurable_id)).norm
  have hmem : MemLp (fun z => ‖fderiv ℝ h (x + z)‖) 2 (gaussianLaw t) :=
    MemLp.of_bound hmeas.aestronglyMeasurable L (Filter.Eventually.of_forall fun z => by
      rw [norm_norm]; exact hL _)
  calc ‖∫ z, fderiv ℝ h (x + z) ∂(gaussianLaw t)‖ ^ 2
      ≤ (∫ z, ‖fderiv ℝ h (x + z)‖ ∂(gaussianLaw t)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_integral_le_integral_norm _) 2
    _ ≤ ∫ z, ‖fderiv ℝ h (x + z)‖ ^ 2 ∂(gaussianLaw t) := sq_integral_le_integral_sq hmem

end KB


-- ===== from Solutions/KB/Post.lean =====

open MeasureTheory ProbabilityTheory
open FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
open scoped RealInnerProductSpace

namespace KB
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- numerator of the posterior average -/
noncomputable def postN (t : ℝ) (ν : Measure V) (w : V → ℝ) (y : V) : ℝ :=
  ∫ x, w x * kernel t (y - x) ∂ν

/-- derivative of the numerator -/
noncomputable def postND (t : ℝ) (ν : Measure V) (w : V → ℝ) (y : V) : V →L[ℝ] ℝ :=
  ∫ x, (w x * (kernel t (y - x) * (-2 * t))) • innerSL ℝ (y - x) ∂ν

/-- posterior average `E[w(X) | X + N(0, I/(2t)) = y]` -/
noncomputable def post (t : ℝ) (ν : Measure V) (w : V → ℝ) (y : V) : ℝ :=
  postN t ν w y / postN t ν (fun _ => 1) y

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem hasFDerivAt_kernel_sub (t : ℝ) (x y : V) :
    HasFDerivAt (fun y => kernel t (y - x))
      ((kernel t (y - x) * (-2 * t)) • innerSL ℝ (y - x)) y := by
  have h1 : HasFDerivAt (fun y : V => ‖y - x‖ ^ 2) ((2 : ℝ) • innerSL ℝ (y - x)) y := by
    have := ((hasFDerivAt_id y).sub_const x).norm_sq
    refine this.congr_fderiv ?_
    ext v
    simp [innerSL_apply_apply, two_smul]
  have h2 := (h1.const_mul (-t)).exp
  refine h2.congr_fderiv ?_
  ext v
  simp [kernel, innerSL_apply_apply]
  ring

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem norm_mul_kernel_le {t : ℝ} (ht : 0 < t) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : V, ‖z‖ * kernel t z ≤ B := by
  obtain ⟨C, hC⟩ := one_add_pow_mul_exp_neg_sq_bounded t ht 1
  refine ⟨max C 0, le_max_right _ _, fun z => ?_⟩
  have := hC ‖z‖ (norm_nonneg _)
  unfold kernel
  have h2 : ‖z‖ * Real.exp (-t * ‖z‖ ^ 2) ≤ (1 + ‖z‖) ^ 1 * Real.exp (-t * ‖z‖ ^ 2) := by
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le; simp
  linarith [le_max_left C 0]

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem kernel_le_one {t : ℝ} (ht : 0 ≤ t) (z : V) : kernel t z ≤ 1 := by
  unfold kernel
  apply Real.exp_le_one_iff.2
  have := sq_nonneg ‖z‖
  nlinarith

variable (ν : Measure V) [IsProbabilityMeasure ν]

theorem hasFDerivAt_postN {t : ℝ} (ht : 0 < t) {w : V → ℝ} (hm : Measurable w) {M : ℝ}
    (hM : ∀ x, |w x| ≤ M) (y0 : V) :
    HasFDerivAt (postN t ν w) (postND t ν w y0) y0 := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM y0)
  obtain ⟨B, hB0, hB⟩ := norm_mul_kernel_le (V := V) ht
  have hkm : Measurable (kernel (V := V) t) := kernel_measurable t
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := ν)
    (F := fun y x => w x * kernel t (y - x))
    (F' := fun y x => (w x * (kernel t (y - x) * (-2 * t))) • innerSL ℝ (y - x))
    (bound := fun _ => M * (2 * t) * B) (Metric.ball_mem_nhds y0 one_pos) ?_ ?_ ?_ ?_
    (integrable_const _) ?_
  · exact Filter.Eventually.of_forall fun y =>
      (hm.mul (hkm.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
  · refine (integrable_const M).mono' (hm.mul (hkm.comp
      (measurable_const.sub measurable_id))).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (kernel_pos t _)]
    calc |w x| * kernel t (y0 - x) ≤ M * 1 :=
          mul_le_mul (hM x) (kernel_le_one ht.le _) (kernel_pos t _).le hM0
      _ = M := mul_one M
  · exact ((hm.mul ((hkm.comp (measurable_const.sub measurable_id)).mul_const _)).smul
      ((innerSL ℝ).continuous.measurable.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x y _ => ?_
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (kernel_pos t _),
      abs_of_neg (by linarith : -2 * t < 0), innerSL_apply_norm, show -(-2 * t) = 2 * t by ring]
    calc |w x| * (kernel t (y - x) * (2 * t)) * ‖y - x‖
        = |w x| * (2 * t) * (‖y - x‖ * kernel t (y - x)) := by ring
      _ ≤ M * (2 * t) * B := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right (hM x) (by linarith)) (hB _)
          (mul_nonneg (norm_nonneg _) (kernel_pos t _).le) (by positivity)
  · refine Filter.Eventually.of_forall fun x y _ => ?_
    exact ((hasFDerivAt_kernel_sub t x y).const_mul (w x)).congr_fderiv (by rw [smul_smul])


omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem sq_mul_kernel_le {t : ℝ} (ht : 0 < t) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : V, ‖z‖ ^ 2 * kernel t z ≤ B := by
  obtain ⟨C, hC⟩ := one_add_pow_mul_exp_neg_sq_bounded t ht 2
  refine ⟨max C 0, le_max_right _ _, fun z => ?_⟩
  have := hC ‖z‖ (norm_nonneg _)
  unfold kernel
  have h2 : ‖z‖ ^ 2 * Real.exp (-t * ‖z‖ ^ 2) ≤ (1 + ‖z‖) ^ 2 * Real.exp (-t * ‖z‖ ^ 2) := by
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    have := norm_nonneg z
    nlinarith
  linarith [le_max_left C 0]

theorem integrable_kernel_sub {t : ℝ} (ht : 0 < t) (y : V) :
    Integrable (fun x => kernel t (y - x)) ν := by
  refine (integrable_const (1:ℝ)).mono' ((kernel_measurable t).comp
    (measurable_const.sub measurable_id)).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_of_nonneg (kernel_pos t _).le]
  exact kernel_le_one ht.le _

theorem postN_one_pos {t : ℝ} (ht : 0 < t) (y : V) : 0 < postN t ν (fun _ => 1) y := by
  unfold postN
  simp only [one_mul]
  rw [integral_pos_iff_support_of_nonneg (fun x => (kernel_pos t _).le) (integrable_kernel_sub ν ht y)]
  have : Function.support (fun x => kernel t (y - x)) = Set.univ := by
    ext x; simp [(kernel_pos t (y - x)).ne']
  rw [this]; simp

/-- the posterior probability measure -/
noncomputable def postMeasure (t : ℝ) (y : V) : Measure V :=
  ν.withDensity (fun x => ENNReal.ofReal (kernel t (y - x) / postN t ν (fun _ => 1) y))

theorem post_eq_integral {t : ℝ} (ht : 0 < t) (g : V → ℝ) (y : V) :
    post t ν g y = ∫ x, g x ∂(postMeasure ν t y) := by
  unfold postMeasure post
  rw [integral_withDensity_eq_integral_toReal_smul (by
      exact ((kernel_measurable t).comp (measurable_const.sub measurable_id)).div_const _
        |>.ennreal_ofReal) (Filter.Eventually.of_forall fun _ => by simp)]
  have hpos := postN_one_pos ν ht y
  set D := postN t ν (fun _ => 1) y
  unfold postN
  rw [← integral_div]
  congr 1; funext x
  rw [ENNReal.toReal_ofReal (div_nonneg (kernel_pos t _).le hpos.le), smul_eq_mul]
  ring

theorem postMeasure_isProb {t : ℝ} (ht : 0 < t) (y : V) : IsProbabilityMeasure (postMeasure ν t y) := by
  constructor
  unfold postMeasure
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_div]
    have : ∫ x, kernel t (y - x) ∂ν = postN t ν (fun _ => 1) y := by unfold postN; simp
    rw [this, div_self (postN_one_pos ν ht y).ne']; simp
  · exact (integrable_kernel_sub ν ht y).div_const _
  · exact Filter.Eventually.of_forall fun x => div_nonneg (kernel_pos t _).le (postN_one_pos ν ht y).le


theorem integrable_mul_inner_kernel {t : ℝ} (ht : 0 < t) {w : V → ℝ} (hm : Measurable w) {M : ℝ}
    (hM : ∀ x, |w x| ≤ M) (v y : V) :
    Integrable (fun x => w x * ⟪v, x⟫ * kernel t (y - x)) ν := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM y)
  obtain ⟨B, hB0, hB⟩ := norm_mul_kernel_le (V := V) ht
  refine (integrable_const (M * ‖v‖ * (‖y‖ + B))).mono' (by
    exact ((hm.mul (measurable_const.inner measurable_id)).mul ((kernel_measurable t).comp
      (measurable_const.sub measurable_id))).aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (kernel_pos t _)]
  have h1 : |⟪v, x⟫| ≤ ‖v‖ * (‖y‖ + ‖y - x‖) := by
    calc |⟪v, x⟫| ≤ ‖v‖ * ‖x‖ := abs_real_inner_le_norm v x
      _ ≤ ‖v‖ * (‖y‖ + ‖y - x‖) := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        calc ‖x‖ = ‖y - (y - x)‖ := by congr 1; abel
          _ ≤ _ := norm_sub_le _ _
  have hk1 := kernel_le_one ht.le (y - x)
  have hk0 := (kernel_pos t (y - x)).le
  have h2 : (‖y‖ + ‖y - x‖) * kernel t (y - x) ≤ ‖y‖ + B := by
    have := hB (y - x); nlinarith [norm_nonneg y]
  calc |w x| * |⟪v, x⟫| * kernel t (y - x) ≤ M * (‖v‖ * (‖y‖ + ‖y - x‖)) * kernel t (y - x) := by
        gcongr
        exact hM x
    _ = M * ‖v‖ * ((‖y‖ + ‖y - x‖) * kernel t (y - x)) := by ring
    _ ≤ M * ‖v‖ * (‖y‖ + B) := by gcongr

theorem postND_apply {t : ℝ} (ht : 0 < t) {w : V → ℝ} (hm : Measurable w) {M : ℝ}
    (hM : ∀ x, |w x| ≤ M) (y v : V) :
    postND t ν w y v = -2 * t * (⟪y, v⟫ * postN t ν w y - postN t ν (fun x => w x * ⟪v, x⟫) y) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM y)
  obtain ⟨B, hB0, hB⟩ := norm_mul_kernel_le (V := V) ht
  have hkm : Measurable (kernel (V := V) t) := kernel_measurable t
  have hint : Integrable (fun x => (w x * (kernel t (y - x) * (-2 * t))) • innerSL ℝ (y - x)) ν := by
    refine (integrable_const (M * (2 * t) * B)).mono' ((hm.mul ((hkm.comp (measurable_const.sub
      measurable_id)).mul_const _)).smul ((innerSL ℝ).continuous.measurable.comp
      (measurable_const.sub measurable_id))).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (kernel_pos t _),
      abs_of_neg (by linarith : -2 * t < 0), innerSL_apply_norm, show -(-2 * t) = 2 * t by ring]
    calc |w x| * (kernel t (y - x) * (2 * t)) * ‖y - x‖
        = |w x| * (2 * t) * (‖y - x‖ * kernel t (y - x)) := by ring
      _ ≤ M * (2 * t) * B := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right (hM x) (by linarith)) (hB _)
          (mul_nonneg (norm_nonneg _) (kernel_pos t _).le) (by positivity)
  unfold postND
  rw [ContinuousLinearMap.integral_apply hint]
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul]
  have hI1 : Integrable (fun x => w x * kernel t (y - x)) ν := by
    refine (integrable_const M).mono' (hm.mul (hkm.comp
      (measurable_const.sub measurable_id))).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (kernel_pos t _)]
    calc |w x| * kernel t (y - x) ≤ M * 1 :=
          mul_le_mul (hM x) (kernel_le_one ht.le _) (kernel_pos t _).le hM0
      _ = M := mul_one M
  have hI2 := integrable_mul_inner_kernel ν ht hm hM v y
  have e : (fun x => w x * (kernel t (y - x) * (-2 * t)) * ⟪y - x, v⟫) =
      fun x => -2 * t * (⟪y, v⟫ * (w x * kernel t (y - x)) - w x * ⟪v, x⟫ * kernel t (y - x)) := by
    funext x
    rw [inner_sub_left, real_inner_comm x v]
    ring
  rw [e, integral_const_mul, integral_sub (hI1.const_mul _) hI2, integral_const_mul]
  unfold postN
  rfl


theorem hasFDerivAt_post {t : ℝ} (ht : 0 < t) {w : V → ℝ} (hm : Measurable w) {M : ℝ}
    (hM : ∀ x, |w x| ≤ M) (y : V) :
    ∃ P : V →L[ℝ] ℝ, HasFDerivAt (post t ν w) P y ∧ ∀ v, P v =
      2 * t * (postN t ν (fun x => w x * ⟪v, x⟫) y / postN t ν (fun _ => 1) y -
        (postN t ν w y / postN t ν (fun _ => 1) y) *
          (postN t ν (fun x => ⟪v, x⟫) y / postN t ν (fun _ => 1) y)) := by
  have hN := hasFDerivAt_postN ν ht hm hM y
  have h1 : ∀ x, |(fun _ : V => (1:ℝ)) x| ≤ 1 := fun x => by simp
  have hD := hasFDerivAt_postN ν ht (w := fun _ => (1:ℝ)) measurable_const h1 y
  have hpos := postN_one_pos ν ht y
  have hinv := (hasFDerivAt_inv hpos.ne').comp y hD
  have hprod := hN.mul hinv
  refine ⟨postN t ν w y • ((ContinuousLinearMap.toSpanSingleton ℝ
      (-(postN t ν (fun _ => 1) y ^ 2)⁻¹)).comp (postND t ν (fun _ => 1) y)) +
      (postN t ν (fun _ => 1) y)⁻¹ • postND t ν w y, ?_, ?_⟩
  · have e : post t ν w = postN t ν w * ((fun x => x⁻¹) ∘ postN t ν fun _ => 1) := by
      funext y; simp [post, div_eq_mul_inv]
    rw [e]; exact hprod
  · intro v
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, smul_eq_mul, ContinuousLinearMap.toSpanSingleton_apply]
    rw [postND_apply ν ht hm hM, postND_apply ν ht measurable_const h1]
    simp only [one_mul]
    field_simp
    ring


theorem integrable_postMeasure_of_bound {t : ℝ} (ht : 0 < t) (y : V) {g : V → ℝ} (hg : Measurable g)
    {C : ℝ} (hC : ∀ x, |g x| * kernel t (y - x) ≤ C) : Integrable g (postMeasure ν t y) := by
  have hpos := postN_one_pos ν ht y
  unfold postMeasure
  have hmeas : Measurable fun x => kernel t (y - x) / postN t ν (fun _ => 1) y :=
    ((kernel_measurable t).comp (measurable_const.sub measurable_id)).div_const _
  rw [integrable_withDensity_iff_integrable_smul' hmeas.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => by simp)]
  · have e : (fun x => (ENNReal.ofReal (kernel t (y - x) / postN t ν (fun _ => 1) y)).toReal • g x) =
        fun x => (kernel t (y - x) / postN t ν (fun _ => 1) y) * g x := by
      funext x
      rw [ENNReal.toReal_ofReal (div_nonneg (kernel_pos t _).le hpos.le), smul_eq_mul]
    rw [e]
    refine (integrable_const (C / postN t ν (fun _ => 1) y)).mono' (hmeas.mul hg).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (div_nonneg (kernel_pos t _).le hpos.le)]
    rw [div_mul_eq_mul_div, mul_comm]
    exact div_le_div_of_nonneg_right (hC x) hpos.le

theorem memLp_inner_postMeasure {t : ℝ} (ht : 0 < t) (y v : V) :
    MemLp (fun x => ⟪v, x⟫) 2 (postMeasure ν t y) := by
  haveI := postMeasure_isProb ν ht y
  obtain ⟨B, hB0, hB⟩ := sq_mul_kernel_le (V := V) ht
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  refine integrable_postMeasure_of_bound ν ht y (by fun_prop) (C := 2 * ‖v‖ ^ 2 * (‖y‖ ^ 2 + B))
    fun x => ?_
  rw [abs_of_nonneg (sq_nonneg _)]
  have h1 : ⟪v, x⟫ ^ 2 ≤ ‖v‖ ^ 2 * (2 * ‖y‖ ^ 2 + 2 * ‖y - x‖ ^ 2) := by
    have hx : ‖x‖ ≤ ‖y‖ + ‖y - x‖ := by
      calc ‖x‖ = ‖y - (y - x)‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    have : ⟪v, x⟫ ^ 2 ≤ (‖v‖ * ‖x‖) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_real_inner_le_norm v x) 2
    have h2 : ‖x‖ ^ 2 ≤ 2 * ‖y‖ ^ 2 + 2 * ‖y - x‖ ^ 2 := by
      have := pow_le_pow_left₀ (norm_nonneg _) hx 2
      nlinarith [sq_nonneg (‖y‖ - ‖y - x‖)]
    calc ⟪v, x⟫ ^ 2 ≤ (‖v‖ * ‖x‖) ^ 2 := this
      _ = ‖v‖ ^ 2 * ‖x‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
  have hk1 := kernel_le_one ht.le (y - x)
  have hk0 := (kernel_pos t (y - x)).le
  have hb := hB (y - x)
  calc ⟪v, x⟫ ^ 2 * kernel t (y - x) ≤ ‖v‖ ^ 2 * (2 * ‖y‖ ^ 2 + 2 * ‖y - x‖ ^ 2) * kernel t (y - x) :=
        mul_le_mul_of_nonneg_right h1 hk0
    _ = 2 * ‖v‖ ^ 2 * (‖y‖ ^ 2 * kernel t (y - x) + ‖y - x‖ ^ 2 * kernel t (y - x)) := by ring
    _ ≤ 2 * ‖v‖ ^ 2 * (‖y‖ ^ 2 + B) := by
        gcongr
        nlinarith [sq_nonneg ‖y‖]

theorem post_div (t : ℝ) (g : V → ℝ) (y : V) :
    postN t ν g y / postN t ν (fun _ => 1) y = post t ν g y := rfl

theorem norm_fderiv_post_sq_le {t : ℝ} (ht : 0 < t) {w : V → ℝ} (hm : Measurable w) {M : ℝ}
    (hM : ∀ x, |w x| ≤ M) (y : V)
    (hvar : ∀ v, variance (fun x => ⟪v, x⟫) (postMeasure ν t y) ≤ ‖v‖ ^ 2 / (2 * t)) :
    ‖fderiv ℝ (post t ν w) y‖ ^ 2 ≤ 2 * t * (post t ν (fun x => w x ^ 2) y - post t ν w y ^ 2) := by
  haveI := postMeasure_isProb ν ht y
  obtain ⟨P, hP, hPv⟩ := hasFDerivAt_post ν ht hm hM y
  rw [hP.fderiv]
  have hwm : MemLp w 2 (postMeasure ν t y) :=
    MemLp.of_bound hm.aestronglyMeasurable M (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hM x)
  have hvarw : variance w (postMeasure ν t y) = post t ν (fun x => w x ^ 2) y - post t ν w y ^ 2 := by
    rw [variance_eq_sub hwm, post_eq_integral ν ht, post_eq_integral ν ht]
    rfl
  have hV0 : 0 ≤ variance w (postMeasure ν t y) := variance_nonneg _ _
  set Var := post t ν (fun x => w x ^ 2) y - post t ν w y ^ 2
  have key : ∀ v, |P v| ≤ Real.sqrt (2 * t * Var) * ‖v‖ := by
    intro v
    have hY := memLp_inner_postMeasure ν ht y v
    have hcov : P v = 2 * t * covariance w (fun x => ⟪v, x⟫) (postMeasure ν t y) := by
      rw [hPv v, covariance_eq_sub hwm hY, post_div, post_div, post_div, post_eq_integral ν ht,
        post_eq_integral ν ht, post_eq_integral ν ht]
      rfl
    have hcs := FunctionalInequalities.Probability.covariance_sq_le_variance_mul_variance_readable hwm hY
    rw [hcov, show Real.sqrt (2 * t * Var) * ‖v‖ = Real.sqrt ((2 * t * Var) * ‖v‖ ^ 2) by
      rw [Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]]
    apply Real.abs_le_sqrt
    rw [mul_pow]
    have h1 : variance w (postMeasure ν t y) * variance (fun x => ⟪v, x⟫) (postMeasure ν t y) ≤
        Var * (‖v‖ ^ 2 / (2 * t)) := by
      rw [hvarw] at hV0 ⊢
      exact mul_le_mul_of_nonneg_left (hvar v) hV0
    calc (2 * t) ^ 2 * covariance w (fun x => ⟪v, x⟫) (postMeasure ν t y) ^ 2
        ≤ (2 * t) ^ 2 * (Var * (‖v‖ ^ 2 / (2 * t))) :=
          mul_le_mul_of_nonneg_left (hcs.trans h1) (by positivity)
      _ = 2 * t * Var * ‖v‖ ^ 2 := by field_simp
  have hle : ‖P‖ ≤ Real.sqrt (2 * t * Var) :=
    ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun v => by
      rw [Real.norm_eq_abs]; exact key v
  calc ‖P‖ ^ 2 ≤ Real.sqrt (2 * t * Var) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hle 2
    _ = 2 * t * Var := Real.sq_sqrt (mul_nonneg (by linarith) (hvarw ▸ hV0))

end KB


-- ===== from Solutions/KB/PostBE.lean =====

open MeasureTheory ProbabilityTheory
open FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
open scoped RealInnerProductSpace ContDiff

namespace KB
variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

theorem norm_gradient_eq (f : E → ℝ) (x : E) : ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  unfold gradient
  exact (InnerProductSpace.toDual ℝ E).symm.norm_map _

theorem postMeasure_eq_posterior (ν : Measure E) [IsProbabilityMeasure ν] {t : ℝ} (ht : 0 < t)
    (y : E) : postMeasure ν t y = PhiSobBayes.posterior ν (2 * t) (Real.sqrt (2 * t) • y) := by
  have hk : ∀ x : E, Real.exp (-‖Real.sqrt (2 * t) • y - Real.sqrt (2 * t) • x‖ ^ 2 / 2) =
      kernel t (y - x) := by
    intro x
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
      Real.sq_sqrt (by linarith)]
    unfold kernel; congr 1; ring
  unfold postMeasure PhiSobBayes.posterior
  congr 1; funext x
  rw [hk]
  congr 2
  unfold postN
  simp only [one_mul]
  congr 1; funext x'; rw [hk]

theorem postMeasure_ac (ν : Measure E) [IsProbabilityMeasure ν] (hν : ν ≪ volume) (t : ℝ) (y : E) :
    postMeasure ν t y ≪ volume :=
  (withDensity_absolutelyContinuous _ _).trans hν

theorem smoothTest_holds_post (ν : Measure E) [IsProbabilityMeasure ν]
    (hν : PhiSobBayes.IsLogConcave ν) {t : ℝ} (ht : 0 < t) (y : E) :
    FunctionalInequalities.Poincare.SmoothTest.Holds (postMeasure ν t y) (1 / (2 * t)) := by
  haveI := postMeasure_isProb ν ht y
  have hslc := PhiSobBayes.lemma_6_1 ν hν (2 * t) (by linarith) (Real.sqrt (2 * t) • y)
  have hP := (PhiSobBayes.fact_A_22 _ (2 * t) (by linarith) hslc).1
  rw [← postMeasure_eq_posterior ν ht y] at hP
  apply FunctionalInequalities.Poincare.SmoothTest.Holds.of_compactSupport_readable (by positivity)
  intro f hf hcs
  have hmem : f ∈ PhiSobBayes.testClass n Set.univ :=
    ⟨⟨0, f, hf.smooth', hcs, by funext x; simp⟩, fun _ => Set.mem_univ _⟩
  exact hP f hmem


/-- Poincaré inequality (constant `1/(2t)`) for the posterior, for `C¹`-type functions with
bounded derivative. -/
theorem post_variance_le (ν : Measure E) [IsProbabilityMeasure ν]
    (hν : PhiSobBayes.IsLogConcave ν) {t : ℝ} (ht : 0 < t) (y : E) {F : E → ℝ}
    (hF : Differentiable ℝ F) {L : ℝ} (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L)
    (hF2 : MemLp F 2 (postMeasure ν t y)) :
    variance F (postMeasure ν t y) ≤ (1 / (2 * t)) * ∫ x, ‖fderiv ℝ F x‖ ^ 2 ∂(postMeasure ν t y) := by
  haveI := postMeasure_isProb ν ht y
  have hνac : ν ≪ volume := by
    obtain ⟨_, V, _, _, _, hV⟩ := hν
    rw [hV]; exact withDensity_absolutelyContinuous _ _
  set π : ProbabilityMeasure E := ⟨postMeasure ν t y, postMeasure_isProb ν ht y⟩
  have hC : (0 : ℝ) ≤ 1 / (2 * t) := by positivity
  have hS := smoothTest_holds_post ν hν ht y
  have hS' : FunctionalInequalities.Poincare.SmoothTest.Holds (π : Measure E)
      (((1 / (2 * t)).toNNReal : NNReal) : ℝ) := by
    rw [Real.coe_toNNReal _ hC]; exact hS
  have hLS := (FunctionalInequalities.Poincare.SmoothTest.holds_iff_localSlope_readable π volume
    (postMeasure_ac ν hνac t y) _).1 hS'
  have hL0 : 0 ≤ L := le_trans (norm_nonneg _) (hL 0)
  have hlip : LipschitzWith (Real.toNNReal L) F :=
    lipschitzWith_of_nnnorm_fderiv_le hF (fun x => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hL0]; exact hL x)
  have hslope : ∀ x, FunctionalInequalities.Energy.LocalSlope.apply F x =
      ENNReal.ofReal ‖fderiv ℝ F x‖ := by
    intro x
    rw [FunctionalInequalities.Energy.LocalSlope.apply_eq_norm_gradient_readable F x (hF x),
      norm_gradient_eq]
  have hint : Integrable (fun x => ‖fderiv ℝ F x‖ ^ 2) (postMeasure ν t y) :=
    (integrable_const (L ^ 2)).mono' ((measurable_fderiv ℝ F).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hL x) 2)
  have henergy : FunctionalInequalities.Energy.LocalSlope.energy π F =
      ENNReal.ofReal (∫ x, ‖fderiv ℝ F x‖ ^ 2 ∂(postMeasure ν t y)) := by
    unfold FunctionalInequalities.Energy.LocalSlope.energy
    simp_rw [hslope]
    rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
    congr 1; funext x
    rw [ENNReal.ofReal_pow (norm_nonneg _)]
  have hadm : FunctionalInequalities.Energy.LocalSlope.Admissible π F :=
    ⟨hlip.locallyLipschitz, hF2, by rw [henergy]; exact ENNReal.ofReal_ne_top⟩
  have h : evariance F (postMeasure ν t y) ≤ _ := hLS F hadm
  rw [henergy] at h
  have hev : evariance F (postMeasure ν t y) ≠ ⊤ := (hF2.evariance_lt_top).ne
  rw [variance, ← ENNReal.toReal_ofReal (mul_nonneg hC (integral_nonneg fun _ => sq_nonneg _))]
  refine ENNReal.toReal_mono ENNReal.ofReal_ne_top ?_
  rw [ENNReal.ofReal_mul hC]
  simpa [Real.coe_toNNReal _ hC, ENNReal.ofReal] using h

theorem post_variance_inner_le (ν : Measure E) [IsProbabilityMeasure ν]
    (hν : PhiSobBayes.IsLogConcave ν) {t : ℝ} (ht : 0 < t) (y v : E) :
    variance (fun x => ⟪v, x⟫) (postMeasure ν t y) ≤ ‖v‖ ^ 2 / (2 * t) := by
  haveI := postMeasure_isProb ν ht y
  have hd : ∀ x, fderiv ℝ (fun x : E => ⟪v, x⟫) x = innerSL ℝ v := by
    intro x; exact ((innerSL ℝ v).hasFDerivAt).fderiv
  have h := post_variance_le ν hν ht y (F := fun x => ⟪v, x⟫) (innerSL ℝ v).differentiable (L := ‖v‖)
    (fun x => by rw [hd]; simp) (memLp_inner_postMeasure ν ht y v)
  simp_rw [hd, innerSL_apply_norm] at h
  simpa [div_eq_inv_mul, mul_comm] using h

end KB


-- ===== from Solutions/KB/Chain.lean =====

open MeasureTheory ProbabilityTheory
open FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
open scoped RealInnerProductSpace

namespace KB
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- bounded measurable functions -/
def BM (f : V → ℝ) : Prop := Measurable f ∧ ∃ M, ∀ x, |f x| ≤ M

variable (ν : Measure V) [IsProbabilityMeasure ν]

theorem integral_conv_gaussian {t : ℝ} (ht : 0 < t) {f : V → ℝ} (hf : BM f) :
    ∫ y, f y ∂(ν.conv (gaussianLaw t)) = ∫ x, heat t f x ∂ν := by
  haveI := gaussianLaw_probability (V := V) ht
  obtain ⟨hm, M, hM⟩ := hf
  unfold Measure.conv
  rw [integral_map (by fun_prop) hm.aestronglyMeasurable]
  rw [integral_prod]
  · congr 1; funext x; rw [heat_eq ht]
  · exact (integrable_const M).mono' (hm.comp (by fun_prop)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => by rw [Real.norm_eq_abs]; exact hM _)

theorem integrable_prod_kernel {t : ℝ} (ht : 0 < t) {G : V → V → ℝ}
    (hG : Measurable (Function.uncurry G)) {C : ℝ} (hC : ∀ x y, |G x y| ≤ C) :
    Integrable (Function.uncurry fun x y => G x y * normalizedKernel t (x - y)) (ν.prod volume) := by
  have hkm : Measurable (normalizedKernel (V := V) t) := normalizedKernel_measurable t
  have hmeas : Measurable (Function.uncurry fun x y => G x y * normalizedKernel t (x - y)) :=
    hG.mul (hkm.comp (measurable_fst.sub measurable_snd))
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  have hC0 : 0 ≤ C := le_trans (abs_nonneg _) (hC 0 0)
  have hk : ∀ x, Integrable (fun y : V => normalizedKernel t (x - y)) :=
    fun x => (integrable_normalizedKernel (V := V) ht).comp_sub_left x
  have hki : ∀ x, ∫ y : V, normalizedKernel t (x - y) = 1 := by
    intro x
    have := integral_sub_left_eq_self (μ := (volume : Measure V)) (fun z => normalizedKernel t z) x
    rw [this, integral_normalizedKernel ht]
  constructor
  · refine Filter.Eventually.of_forall fun x => ((hk x).const_mul C).mono'
      (hmeas.comp (measurable_prodMk_left)).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    simp only [Function.uncurry_apply_pair]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (normalizedKernel_pos ht _)]
    exact mul_le_mul_of_nonneg_right (hC x y) (normalizedKernel_pos ht _).le
  · refine (integrable_const C).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (hmeas.norm.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      calc ∫ y, ‖G x y * normalizedKernel t (x - y)‖ ≤ ∫ y, C * normalizedKernel t (x - y) := by
            apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
              ((hk x).const_mul C) (Filter.Eventually.of_forall fun y => ?_)
            simp only
            rw [Real.norm_eq_abs, abs_mul, abs_of_pos (normalizedKernel_pos ht _)]
            exact mul_le_mul_of_nonneg_right (hC x y) (normalizedKernel_pos ht _).le
        _ = C := by rw [integral_const_mul, hki, mul_one]


theorem post_abs_le {t : ℝ} (ht : 0 < t) {w : V → ℝ} {M : ℝ} (hM : ∀ x, |w x| ≤ M) (y : V) :
    |post t ν w y| ≤ M := by
  haveI := postMeasure_isProb ν ht y
  rw [post_eq_integral ν ht]
  calc |∫ x, w x ∂(postMeasure ν t y)| ≤ ∫ x, |w x| ∂(postMeasure ν t y) :=
        abs_integral_le_integral_abs
    _ ≤ ∫ _x, M ∂(postMeasure ν t y) :=
        integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
          (integrable_const M) (Filter.Eventually.of_forall hM)
    _ = M := by simp

theorem differentiable_post {t : ℝ} (ht : 0 < t) {w : V → ℝ} (hw : BM w) :
    Differentiable ℝ (post t ν w) := fun y => by
  obtain ⟨hm, M, hM⟩ := hw
  obtain ⟨P, hP, -⟩ := hasFDerivAt_post ν ht hm hM y
  exact hP.differentiableAt

theorem post_BM {t : ℝ} (ht : 0 < t) {w : V → ℝ} (hw : BM w) : BM (post t ν w) :=
  ⟨(differentiable_post ν ht hw).continuous.measurable, hw.2.choose,
    post_abs_le ν ht hw.2.choose_spec⟩

theorem heat_BM {t : ℝ} (ht : 0 < t) {h : V → ℝ} (hh : BM h) : BM (heat t h) := by
  obtain ⟨hm, M, hM⟩ := hh
  refine ⟨?_, M, heat_abs_le ht hM⟩
  have hd : Differentiable ℝ (heat t h) := fun x => (hasFDerivAt_heat' ht hm hM x).differentiableAt
  exact hd.continuous.measurable

theorem BM.mul {f g : V → ℝ} (hf : BM f) (hg : BM g) : BM (fun x => f x * g x) := by
  obtain ⟨hfm, A, hA⟩ := hf
  obtain ⟨hgm, B, hB⟩ := hg
  refine ⟨hfm.mul hgm, A * B, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (hA x) (hB x) (abs_nonneg _) (le_trans (abs_nonneg _) (hA x))

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem normalizedKernel_symm (t : ℝ) (x y : V) :
    normalizedKernel t (x - y) = kernel t (y - x) / mass (V := V) t := by
  unfold normalizedKernel kernel
  rw [norm_sub_rev]

/-- Bayes / detailed balance identity for the Gaussian channel. -/
theorem bayes {t : ℝ} (ht : 0 < t) {g w : V → ℝ} (hg : BM g) (hw : BM w) :
    ∫ y, g y * post t ν w y ∂(ν.conv (gaussianLaw t)) = ∫ x, heat t g x * w x ∂ν := by
  have hpw := post_BM ν ht hw
  obtain ⟨hgm, Mg, hMg⟩ := hg
  obtain ⟨hwm, Mw, hMw⟩ := hw
  obtain ⟨hpm, Mp, hMp⟩ := hpw
  have hmass := mass_pos (V := V) ht
  rw [integral_conv_gaussian ν ht ((show BM g from ⟨hgm, Mg, hMg⟩).mul ⟨hpm, Mp, hMp⟩)]
  unfold heat
  simp only []
  have hb1 : ∀ x y : V, |(fun (_ : V) (y : V) => g y * post t ν w y) x y| ≤ Mg * Mp := by
    intro x y
    simp only [abs_mul]
    exact mul_le_mul (hMg y) (hMp y) (abs_nonneg _) (le_trans (abs_nonneg _) (hMg y))
  have hb2 : ∀ x y : V, |(fun (x : V) (y : V) => g y * w x) x y| ≤ Mg * Mw := by
    intro x y
    simp only [abs_mul]
    exact mul_le_mul (hMg y) (hMw x) (abs_nonneg _) (le_trans (abs_nonneg _) (hMg y))
  rw [integral_integral_swap (integrable_prod_kernel ν ht (G := fun _ y => g y * post t ν w y)
    ((hgm.comp measurable_snd).mul (hpm.comp measurable_snd)) hb1)]
  have step : ∀ y, ∫ x, g y * post t ν w y * normalizedKernel t (x - y) ∂ν =
      ∫ x, g y * w x * normalizedKernel t (x - y) ∂ν := by
    intro y
    have hD := postN_one_pos ν ht y
    simp_rw [normalizedKernel_symm]
    rw [integral_const_mul, integral_div]
    have e2 : ∫ x, g y * w x * (kernel t (y - x) / mass (V := V) t) ∂ν =
        g y * postN t ν w y / mass (V := V) t := by
      unfold postN
      rw [← integral_const_mul, ← integral_div]
      congr 1; funext x; ring
    rw [e2]
    have e3 : ∫ x, kernel t (y - x) ∂ν = postN t ν (fun _ => 1) y := by unfold postN; simp
    rw [e3]
    unfold post
    field_simp
  simp_rw [step]
  rw [← integral_integral_swap (integrable_prod_kernel ν ht (G := fun x y => g y * w x)
    ((hgm.comp measurable_snd).mul (hwm.comp measurable_fst)) hb2)]
  congr 1; funext x
  rw [← integral_mul_const]
  congr 1; funext y; ring

end KB


-- ===== from Solutions/KB/Kc.lean =====

open MeasureTheory ProbabilityTheory
open FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
open scoped RealInnerProductSpace

namespace KB
variable {n : ℕ}

/-- one step of the Gaussian-channel chain -/
noncomputable def Kc (t : ℝ) (ν : Measure (EuclideanSpace ℝ (Fin n))) (h : (EuclideanSpace ℝ (Fin n)) → ℝ) : (EuclideanSpace ℝ (Fin n)) → ℝ := post t ν (heat t h)

variable (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]

theorem Kc_BM {t : ℝ} (ht : 0 < t) {h : (EuclideanSpace ℝ (Fin n)) → ℝ} (hh : BM h) : BM (Kc t ν h) :=
  post_BM ν ht (heat_BM ht hh)

theorem heat_mono {t : ℝ} (ht : 0 < t) {h h' : (EuclideanSpace ℝ (Fin n)) → ℝ} (hh : BM h) (hh' : BM h')
    (hle : ∀ x, h x ≤ h' x) (x : (EuclideanSpace ℝ (Fin n))) : heat t h x ≤ heat t h' x := by
  haveI := gaussianLaw_probability (V := EuclideanSpace ℝ (Fin n)) ht
  rw [heat_eq ht, heat_eq ht]
  obtain ⟨hm, M, hM⟩ := hh
  obtain ⟨hm', M', hM'⟩ := hh'
  apply integral_mono
  · exact (integrable_const M).mono' (hm.comp (by fun_prop)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hM _)
  · exact (integrable_const M').mono' (hm'.comp (by fun_prop)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hM' _)
  · exact fun z => hle _

theorem post_mono {t : ℝ} (ht : 0 < t) {w w' : (EuclideanSpace ℝ (Fin n)) → ℝ} (hw : BM w) (hw' : BM w')
    (hle : ∀ x, w x ≤ w' x) (y : (EuclideanSpace ℝ (Fin n))) : post t ν w y ≤ post t ν w' y := by
  haveI := postMeasure_isProb ν ht y
  rw [post_eq_integral ν ht, post_eq_integral ν ht]
  obtain ⟨hm, M, hM⟩ := hw
  obtain ⟨hm', M', hM'⟩ := hw'
  apply integral_mono
  · exact (integrable_const M).mono' hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hM _)
  · exact (integrable_const M').mono' hm'.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hM' _)
  · exact hle

theorem Kc_mono {t : ℝ} (ht : 0 < t) {h h' : (EuclideanSpace ℝ (Fin n)) → ℝ} (hh : BM h) (hh' : BM h')
    (hle : ∀ x, h x ≤ h' x) (y : (EuclideanSpace ℝ (Fin n))) : Kc t ν h y ≤ Kc t ν h' y :=
  post_mono ν ht (heat_BM ht hh) (heat_BM ht hh') (heat_mono ht hh hh' hle) y

theorem heat_sq_le {t : ℝ} (ht : 0 < t) {h : (EuclideanSpace ℝ (Fin n)) → ℝ} (hh : BM h) (x : (EuclideanSpace ℝ (Fin n))) :
    heat t h x ^ 2 ≤ heat t (fun y => h y ^ 2) x := by
  haveI := gaussianLaw_probability (V := EuclideanSpace ℝ (Fin n)) ht
  obtain ⟨hm, M, hM⟩ := hh
  rw [heat_eq ht, heat_eq ht]
  exact sq_integral_le_integral_sq (MemLp.of_bound (hm.comp (by fun_prop)).aestronglyMeasurable M
    (Filter.Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact hM _))

theorem BM.sq {h : (EuclideanSpace ℝ (Fin n)) → ℝ} (hh : BM h) : BM (fun y => h y ^ 2) := by
  have := hh.mul hh
  have e : (fun y => h y ^ 2) = fun y => h y * h y := by funext y; ring
  rw [e]; exact this

/-- (G2): the reverse local Poincaré inequality for one step of the chain. -/
theorem Kc_grad_sq_le_var (hν : PhiSobBayes.IsLogConcave ν) {t : ℝ} (ht : 0 < t) {h : (EuclideanSpace ℝ (Fin n)) → ℝ}
    (hh : BM h) (y : (EuclideanSpace ℝ (Fin n))) :
    ‖fderiv ℝ (Kc t ν h) y‖ ^ 2 ≤ 2 * t * (Kc t ν (fun x => h x ^ 2) y - Kc t ν h y ^ 2) := by
  have hH := heat_BM ht hh
  have hH2 := BM.sq hH
  obtain ⟨hHm, M, hM⟩ := hH
  have h1 := norm_fderiv_post_sq_le ν ht hHm hM y (post_variance_inner_le ν hν ht y)
  unfold Kc
  refine h1.trans ?_
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  have := post_mono ν ht hH2 (heat_BM ht hh.sq) (heat_sq_le ht hh) y
  linarith


theorem BM_grad_sq {h : (EuclideanSpace ℝ (Fin n)) → ℝ} {L : ℝ}
    (hL : ∀ x, ‖fderiv ℝ h x‖ ≤ L) : BM (fun x => ‖fderiv ℝ h x‖ ^ 2) := by
  refine ⟨(measurable_fderiv ℝ h).norm.pow_const 2, L ^ 2, fun x => ?_⟩
  rw [abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hL x) 2

theorem heat_grad_le {t : ℝ} (ht : 0 < t) {h : (EuclideanSpace ℝ (Fin n)) → ℝ} (hh : BM h)
    (hd : Differentiable ℝ h) {L : ℝ} (hL : ∀ x, ‖fderiv ℝ h x‖ ≤ L) (x : EuclideanSpace ℝ (Fin n)) :
    ‖fderiv ℝ (heat t h) x‖ ≤ L := by
  have hL0 : 0 ≤ L := le_trans (norm_nonneg _) (hL 0)
  obtain ⟨hm, M, hM⟩ := hh
  have h1 := norm_fderiv_heat_sq_le_of_differentiable ht hd hL hM x
  have h2 := heat_abs_le ht (h := fun y => ‖fderiv ℝ h y‖ ^ 2) (M := L ^ 2) (fun y => by
    rw [abs_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (norm_nonneg _) (hL y) 2) x
  have h3 : ‖fderiv ℝ (heat t h) x‖ ^ 2 ≤ L ^ 2 := h1.trans (le_trans (le_abs_self _) h2)
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hL0 (by norm_num)).1 h3

theorem differentiable_heat_of_differentiable {t : ℝ} (ht : 0 < t) {h : (EuclideanSpace ℝ (Fin n)) → ℝ}
    (hh : BM h) (hd : Differentiable ℝ h) {L : ℝ} (hL : ∀ x, ‖fderiv ℝ h x‖ ≤ L) :
    Differentiable ℝ (heat t h) := fun x =>
  (hasFDerivAt_heat_of_differentiable ht hd hL hh.2.choose_spec x).differentiableAt

/-- (G1): gradient sub-commutation for one step of the chain. -/
theorem Kc_grad_sq_le (hν : PhiSobBayes.IsLogConcave ν) {t : ℝ} (ht : 0 < t)
    {h : (EuclideanSpace ℝ (Fin n)) → ℝ} (hh : BM h) (hd : Differentiable ℝ h) {L : ℝ}
    (hL : ∀ x, ‖fderiv ℝ h x‖ ≤ L) (y : EuclideanSpace ℝ (Fin n)) :
    ‖fderiv ℝ (Kc t ν h) y‖ ^ 2 ≤ Kc t ν (fun x => ‖fderiv ℝ h x‖ ^ 2) y := by
  haveI := postMeasure_isProb ν ht y
  have hH := heat_BM ht hh
  obtain ⟨hHm, M, hM⟩ := hH
  have h1 := norm_fderiv_post_sq_le ν ht hHm hM y (post_variance_inner_le ν hν ht y)
  have hwm : MemLp (heat t h) 2 (postMeasure ν t y) :=
    MemLp.of_bound hHm.aestronglyMeasurable M (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hM x)
  have hvarw : variance (heat t h) (postMeasure ν t y) =
      post t ν (fun x => heat t h x ^ 2) y - post t ν (heat t h) y ^ 2 := by
    rw [variance_eq_sub hwm, post_eq_integral ν ht, post_eq_integral ν ht]
    rfl
  have hdH := differentiable_heat_of_differentiable ht hh hd hL
  have hLH := heat_grad_le ht hh hd hL
  have h2 := post_variance_le ν hν ht y hdH hLH hwm
  -- ∫ ‖∇ heat h‖² dπ ≤ post (heat ‖∇h‖²)
  have hG := BM_grad_sq hL
  have h3 : ∫ x, ‖fderiv ℝ (heat t h) x‖ ^ 2 ∂(postMeasure ν t y) ≤
      Kc t ν (fun x => ‖fderiv ℝ h x‖ ^ 2) y := by
    unfold Kc
    rw [post_eq_integral ν ht]
    have hb := heat_BM ht hG
    apply integral_mono
    · exact (integrable_const (L ^ 2)).mono' ((measurable_fderiv ℝ _).norm.pow_const 2).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          rw [Real.norm_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (norm_nonneg _) (hLH x) 2)
    · exact (integrable_const hb.2.choose).mono' hb.1.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb.2.choose_spec x)
    · intro x
      obtain ⟨hm, M', hM'⟩ := hh
      exact norm_fderiv_heat_sq_le_of_differentiable ht hd hL hM' x
  unfold Kc
  calc ‖fderiv ℝ (post t ν (heat t h)) y‖ ^ 2
      ≤ 2 * t * (post t ν (fun x => heat t h x ^ 2) y - post t ν (heat t h) y ^ 2) := h1
    _ = 2 * t * variance (heat t h) (postMeasure ν t y) := by rw [hvarw]
    _ ≤ 2 * t * ((1 / (2 * t)) * ∫ x, ‖fderiv ℝ (heat t h) x‖ ^ 2 ∂(postMeasure ν t y)) :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
    _ = ∫ x, ‖fderiv ℝ (heat t h) x‖ ^ 2 ∂(postMeasure ν t y) := by field_simp
    _ ≤ Kc t ν (fun x => ‖fderiv ℝ h x‖ ^ 2) y := h3


section Linear
variable {t : ℝ} (ht : 0 < t)
include ht

omit ht in
theorem BM.integrable {μ : Measure (EuclideanSpace ℝ (Fin n))} [IsFiniteMeasure μ]
    {h : (EuclideanSpace ℝ (Fin n)) → ℝ} (hh : BM h) : Integrable h μ :=
  (integrable_const hh.2.choose).mono' hh.1.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hh.2.choose_spec x)

omit ht in
theorem BM.add {a b : (EuclideanSpace ℝ (Fin n)) → ℝ} (ha : BM a) (hb : BM b) :
    BM (fun x => a x + b x) := by
  obtain ⟨am, A, hA⟩ := ha
  obtain ⟨bm, B, hB⟩ := hb
  exact ⟨am.add bm, A + B, fun x => (abs_add_le _ _).trans (add_le_add (hA x) (hB x))⟩

omit ht in
theorem BM.const_mul {a : (EuclideanSpace ℝ (Fin n)) → ℝ} (ha : BM a) (c : ℝ) :
    BM (fun x => c * a x) := by
  obtain ⟨am, A, hA⟩ := ha
  exact ⟨am.const_mul c, |c| * A, fun x => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hA x) (abs_nonneg _)⟩

theorem heat_add {a b : (EuclideanSpace ℝ (Fin n)) → ℝ} (ha : BM a) (hb : BM b) (x : EuclideanSpace ℝ (Fin n)) :
    heat t (fun y => a y + b y) x = heat t a x + heat t b x := by
  haveI := gaussianLaw_probability (V := EuclideanSpace ℝ (Fin n)) ht
  rw [heat_eq ht, heat_eq ht, heat_eq ht]
  have hca : BM (fun z => a (x + z)) := ⟨ha.1.comp (by fun_prop), ha.2.choose, fun z => ha.2.choose_spec _⟩
  have hcb : BM (fun z => b (x + z)) := ⟨hb.1.comp (by fun_prop), hb.2.choose, fun z => hb.2.choose_spec _⟩
  exact integral_add hca.integrable hcb.integrable

theorem heat_const_mul {a : (EuclideanSpace ℝ (Fin n)) → ℝ} (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    heat t (fun y => c * a y) x = c * heat t a x := by
  rw [heat_eq ht, heat_eq ht, integral_const_mul]

theorem heat_const (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) : heat t (fun _ => c) x = c := by
  haveI := gaussianLaw_probability (V := EuclideanSpace ℝ (Fin n)) ht
  rw [heat_eq ht]; simp

theorem post_add {a b : (EuclideanSpace ℝ (Fin n)) → ℝ} (ha : BM a) (hb : BM b) (y : EuclideanSpace ℝ (Fin n)) :
    post t ν (fun x => a x + b x) y = post t ν a y + post t ν b y := by
  haveI := postMeasure_isProb ν ht y
  rw [post_eq_integral ν ht, post_eq_integral ν ht, post_eq_integral ν ht]
  exact integral_add ha.integrable hb.integrable

theorem post_const_mul {a : (EuclideanSpace ℝ (Fin n)) → ℝ} (c : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    post t ν (fun x => c * a x) y = c * post t ν a y := by
  rw [post_eq_integral ν ht, post_eq_integral ν ht, integral_const_mul]

theorem post_const (c : ℝ) (y : EuclideanSpace ℝ (Fin n)) : post t ν (fun _ => c) y = c := by
  haveI := postMeasure_isProb ν ht y
  rw [post_eq_integral ν ht]; simp

theorem Kc_add {a b : (EuclideanSpace ℝ (Fin n)) → ℝ} (ha : BM a) (hb : BM b) :
    Kc t ν (fun x => a x + b x) = fun y => Kc t ν a y + Kc t ν b y := by
  funext y
  unfold Kc
  have e : heat t (fun y => a y + b y) = fun x => heat t a x + heat t b x := by
    funext x; exact heat_add ht ha hb x
  rw [e, post_add ν ht (heat_BM ht ha) (heat_BM ht hb)]

theorem Kc_const_mul {a : (EuclideanSpace ℝ (Fin n)) → ℝ} (c : ℝ) :
    Kc t ν (fun x => c * a x) = fun y => c * Kc t ν a y := by
  funext y
  unfold Kc
  have e : heat t (fun y => c * a y) = fun x => c * heat t a x := by
    funext x; exact heat_const_mul ht c x
  rw [e, post_const_mul ν ht]

theorem Kc_const (c : ℝ) : Kc t ν (fun _ => c) = fun _ => c := by
  funext y
  unfold Kc
  have e : heat t (fun _ : EuclideanSpace ℝ (Fin n) => c) = fun _ => c := by
    funext x; exact heat_const ht c x
  rw [e, post_const ν ht]

theorem Kc_abs_le {h : (EuclideanSpace ℝ (Fin n)) → ℝ} {M : ℝ} (hM : ∀ x, |h x| ≤ M)
    (y : EuclideanSpace ℝ (Fin n)) : |Kc t ν h y| ≤ M :=
  post_abs_le ν ht (heat_abs_le ht hM) y

theorem iterate_BM {h : (EuclideanSpace ℝ (Fin n)) → ℝ} (hh : BM h) (k : ℕ) : BM ((Kc t ν)^[k] h) := by
  induction k with
  | zero => simpa
  | succ k ih => rw [Function.iterate_succ_apply']; exact Kc_BM ν ht ih

theorem iterate_abs_le {h : (EuclideanSpace ℝ (Fin n)) → ℝ} {M : ℝ} (hM : ∀ x, |h x| ≤ M) (k : ℕ)
    (y : EuclideanSpace ℝ (Fin n)) : |(Kc t ν)^[k] h y| ≤ M := by
  induction k generalizing y with
  | zero => simpa using hM y
  | succ k ih => rw [Function.iterate_succ_apply']; exact Kc_abs_le ν ht ih y

theorem iterate_mono {h h' : (EuclideanSpace ℝ (Fin n)) → ℝ} (hh : BM h) (hh' : BM h')
    (hle : ∀ x, h x ≤ h' x) (k : ℕ) (y : EuclideanSpace ℝ (Fin n)) :
    (Kc t ν)^[k] h y ≤ (Kc t ν)^[k] h' y := by
  induction k generalizing y with
  | zero => simpa using hle y
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact Kc_mono ν ht (iterate_BM ν ht hh k) (iterate_BM ν ht hh' k) ih y

theorem iterate_add {a b : (EuclideanSpace ℝ (Fin n)) → ℝ} (ha : BM a) (hb : BM b) (k : ℕ) :
    (Kc t ν)^[k] (fun x => a x + b x) = fun y => (Kc t ν)^[k] a y + (Kc t ν)^[k] b y := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      Kc_add ν ht (iterate_BM ν ht ha k) (iterate_BM ν ht hb k)]

theorem iterate_const_mul {a : (EuclideanSpace ℝ (Fin n)) → ℝ} (c : ℝ) (k : ℕ) :
    (Kc t ν)^[k] (fun x => c * a x) = fun y => c * (Kc t ν)^[k] a y := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, Kc_const_mul ν ht]

theorem iterate_sub {a b : (EuclideanSpace ℝ (Fin n)) → ℝ} (ha : BM a) (hb : BM b) (k : ℕ) :
    (Kc t ν)^[k] (fun x => a x - b x) = fun y => (Kc t ν)^[k] a y - (Kc t ν)^[k] b y := by
  have e : (fun x => a x - b x) = fun x => a x + (-1) * b x := by funext x; ring
  rw [e, iterate_add ν ht ha (hb.const_mul (-1)), iterate_const_mul ν ht]
  funext y; ring

theorem iterate_const (c : ℝ) (k : ℕ) : (Kc t ν)^[k] (fun _ => c) = fun _ => c := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, Kc_const ν ht]

end Linear


section Iter
variable {t : ℝ} (ht : 0 < t) (hν : PhiSobBayes.IsLogConcave ν)
include ht hν

omit hν in
theorem differentiable_Kc {h : (EuclideanSpace ℝ (Fin n)) → ℝ} (hh : BM h) :
    Differentiable ℝ (Kc t ν h) :=
  differentiable_post ν ht (heat_BM ht hh)

theorem iterate_grad_sq_le {h : (EuclideanSpace ℝ (Fin n)) → ℝ} (hh : BM h) (hd : Differentiable ℝ h)
    {L : ℝ} (hL : ∀ x, ‖fderiv ℝ h x‖ ≤ L) (k : ℕ) :
    Differentiable ℝ ((Kc t ν)^[k] h) ∧ ∀ y, ‖fderiv ℝ ((Kc t ν)^[k] h) y‖ ^ 2 ≤
      (Kc t ν)^[k] (fun x => ‖fderiv ℝ h x‖ ^ 2) y := by
  have hL0 : 0 ≤ L := le_trans (norm_nonneg _) (hL 0)
  have hG := BM_grad_sq hL
  induction k with
  | zero => exact ⟨hd, fun y => le_rfl⟩
  | succ k ih =>
    obtain ⟨hdk, hbk⟩ := ih
    set g := (Kc t ν)^[k] h
    have hgBM : BM g := iterate_BM ν ht hh k
    have hgL : ∀ x, ‖fderiv ℝ g x‖ ≤ L := by
      intro x
      have h1 := hbk x
      have h2 := iterate_abs_le ν ht (h := fun x => ‖fderiv ℝ h x‖ ^ 2) (M := L ^ 2) (fun x => by
        rw [abs_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (norm_nonneg _) (hL x) 2) k x
      have h3 : ‖fderiv ℝ g x‖ ^ 2 ≤ L ^ 2 := h1.trans (le_trans (le_abs_self _) h2)
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) hL0 (by norm_num)).1 h3
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    refine ⟨differentiable_Kc ν ht hgBM, fun y => ?_⟩
    calc ‖fderiv ℝ (Kc t ν g) y‖ ^ 2 ≤ Kc t ν (fun x => ‖fderiv ℝ g x‖ ^ 2) y :=
          Kc_grad_sq_le ν hν ht hgBM hdk hgL y
      _ ≤ Kc t ν ((Kc t ν)^[k] fun x => ‖fderiv ℝ h x‖ ^ 2) y :=
          Kc_mono ν ht (BM_grad_sq hgL) (iterate_BM ν ht hG k) hbk y

theorem Kc_grad_le_of_abs_le {g : (EuclideanSpace ℝ (Fin n)) → ℝ} (hg : BM g) {M : ℝ}
    (hM : ∀ x, |g x| ≤ M) (y : EuclideanSpace ℝ (Fin n)) :
    ‖fderiv ℝ (Kc t ν g) y‖ ≤ Real.sqrt (2 * t) * M := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have h1 := Kc_grad_sq_le_var ν hν ht hg y
  have h2 : Kc t ν (fun x => g x ^ 2) y ≤ M ^ 2 := by
    have := Kc_abs_le ν ht (h := fun x => g x ^ 2) (M := M ^ 2) (fun x => by
      rw [abs_of_nonneg (sq_nonneg _)]
      exact (sq_le_sq₀ (abs_nonneg _) hM0).2 (hM x) |> fun h => by simpa [sq_abs] using h) y
    exact le_trans (le_abs_self _) this
  have h3 : ‖fderiv ℝ (Kc t ν g) y‖ ^ 2 ≤ (Real.sqrt (2 * t) * M) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by linarith)]
    nlinarith [sq_nonneg (Kc t ν g y)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).1 h3

/-- Bakry–Ledoux iteration for the chain. -/
theorem iterate_grad_bound (k : ℕ) : ∀ {g : (EuclideanSpace ℝ (Fin n)) → ℝ}, BM g →
    ∀ y, (k : ℝ) * ‖fderiv ℝ ((Kc t ν)^[k] g) y‖ ^ 2 ≤
      2 * t * ((Kc t ν)^[k] (fun x => g x ^ 2) y - ((Kc t ν)^[k] g y) ^ 2) := by
  induction k with
  | zero => intro g hg y; simp
  | succ k ih =>
    intro g hg y
    obtain ⟨hgm, M, hM⟩ := hg
    have hg : BM g := ⟨hgm, M, hM⟩
    set g1 := Kc t ν g
    have hg1 : BM g1 := Kc_BM ν ht hg
    have hd1 : Differentiable ℝ g1 := differentiable_Kc ν ht hg
    have hL1 := Kc_grad_le_of_abs_le ν ht hν hg hM
    have hA := (iterate_grad_sq_le ν ht hν hg1 hd1 hL1 k).2 y
    have hIH := ih hg1 y
    -- D := Kc(g²) - g1²
    have hg2 : BM (fun x => g x ^ 2) := BM.sq hg
    have hKg2 : BM (Kc t ν fun x => g x ^ 2) := Kc_BM ν ht hg2
    have hg1sq : BM (fun x => g1 x ^ 2) := BM.sq hg1
    have hpt : ∀ x, ‖fderiv ℝ g1 x‖ ^ 2 ≤
        2 * t * (Kc t ν (fun x => g x ^ 2) x - g1 x ^ 2) := fun x => Kc_grad_sq_le_var ν hν ht hg x
    have hD : BM (fun x => 2 * t * (Kc t ν (fun x => g x ^ 2) x - g1 x ^ 2)) := by
      have := (hKg2.add (hg1sq.const_mul (-1))).const_mul (2 * t)
      convert this using 2 with x; ring
    have hmono := iterate_mono ν ht (BM_grad_sq hL1) hD hpt k y
    have hlin : (Kc t ν)^[k] (fun x => 2 * t * (Kc t ν (fun x => g x ^ 2) x - g1 x ^ 2)) y =
        2 * t * ((Kc t ν)^[k] (Kc t ν fun x => g x ^ 2) y - (Kc t ν)^[k] (fun x => g1 x ^ 2) y) := by
      rw [iterate_const_mul ν ht, iterate_sub ν ht hKg2 hg1sq]
    rw [hlin] at hmono
    simp only [Function.iterate_succ_apply]
    push_cast
    nlinarith [hA, hIH, hmono]

end Iter

end KB


-- ===== from Solutions/KB/GaussIneq.lean =====

open MeasureTheory ProbabilityTheory
open FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
open scoped RealInnerProductSpace

namespace KB
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

theorem integrable_norm_mul_normalizedKernel {t : ℝ} (ht : 0 < t) :
    Integrable (fun b : V => ‖b‖ * normalizedKernel t b) := by
  have h := (integrable_poly_kernel (V := V) ht 0).div_const (mass (V := V) t)
  refine h.mono' (by
    exact (measurable_norm.mul (normalizedKernel_measurable t)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun b => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (normalizedKernel_pos ht _).le)]
  unfold normalizedKernel kernel
  simp only [zero_sub, norm_neg]
  rw [mul_div_assoc']
  apply div_le_div_of_nonneg_right _ (mass_pos ht).le
  have h1 : Real.exp (-t * ‖b‖ ^ 2) ≤ Real.exp (-(t / 2) * ‖b‖ ^ 2) := by
    apply Real.exp_le_exp.2; nlinarith [sq_nonneg ‖b‖]
  nlinarith [norm_nonneg b, Real.exp_pos (-t * ‖b‖ ^ 2)]

/-- Gaussian integration by parts (Stein's identity) for differentiable functions with bounded
derivative. -/
theorem stein {t : ℝ} (ht : 0 < t) {f : V → ℝ} (hf : Differentiable ℝ f) {M L : ℝ}
    (hM : ∀ b, |f b| ≤ M) (hL : ∀ b, ‖fderiv ℝ f b‖ ≤ L) (u : V) :
    ∫ b, ⟪u, b⟫ * f b ∂(gaussianLaw t) = (2 * t)⁻¹ * ∫ b, fderiv ℝ f b u ∂(gaussianLaw t) := by
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hL0 : 0 ≤ L := le_trans (norm_nonneg _) (hL 0)
  have hkm : Measurable (normalizedKernel (V := V) t) := normalizedKernel_measurable t
  have hdk : ∀ b, HasFDerivAt (normalizedKernel (V := V) t)
      ((normalizedKernel t b * (-2 * t)) • innerSL ℝ b) b := by
    intro b
    have := hasFDerivAt_normalizedKernel_sub (V := V) t b 0
    simpa using this
  have hdk' : ∀ b, fderiv ℝ (normalizedKernel (V := V) t) b u = normalizedKernel t b * (-2 * t) * ⟪b, u⟫ := by
    intro b; rw [(hdk b).fderiv]; simp [innerSL_apply_apply]
  have hwd : ∀ g : V → ℝ, ∫ b, g b ∂(gaussianLaw t) = ∫ b, g b * normalizedKernel t b := by
    intro g
    rw [gaussianLaw, integral_withDensity_eq_integral_toReal_smul hkm.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => by simp)]
    congr 1; funext b
    rw [ENNReal.toReal_ofReal (normalizedKernel_pos ht b).le, smul_eq_mul, mul_comm]
  rw [hwd, hwd]
  have hfm : Measurable f := hf.continuous.measurable
  have hI1 : Integrable (fun b => fderiv ℝ f b u * normalizedKernel t b) := by
    refine ((integrable_normalizedKernel (V := V) ht).const_mul (L * ‖u‖)).mono'
      ((measurable_fderiv_apply_const ℝ f u).mul hkm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun b => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (normalizedKernel_pos ht b)]
    apply mul_le_mul_of_nonneg_right _ (normalizedKernel_pos ht b).le
    calc |fderiv ℝ f b u| ≤ ‖fderiv ℝ f b‖ * ‖u‖ := by
          rw [← Real.norm_eq_abs]; exact (fderiv ℝ f b).le_opNorm u
      _ ≤ L * ‖u‖ := mul_le_mul_of_nonneg_right (hL b) (norm_nonneg _)
  have hI2 : Integrable (fun b => f b * fderiv ℝ (normalizedKernel (V := V) t) b u) := by
    simp_rw [hdk']
    refine ((integrable_norm_mul_normalizedKernel (V := V) ht).const_mul (M * 2 * t * ‖u‖)).mono'
      (by exact (hfm.mul ((hkm.mul_const _).mul (measurable_id.inner measurable_const))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun b => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_of_pos (normalizedKernel_pos ht b),
      abs_of_neg (by linarith : -2 * t < 0)]
    have h1 := abs_real_inner_le_norm b u
    have h2 := hM b
    have hk := (normalizedKernel_pos ht b).le
    calc |f b| * (normalizedKernel t b * -(-2 * t) * |⟪b, u⟫|)
        ≤ M * (normalizedKernel t b * (2 * t) * (‖b‖ * ‖u‖)) := by
          rw [show -(-2 * t) = 2 * t by ring]
          gcongr
      _ = M * 2 * t * ‖u‖ * (‖b‖ * normalizedKernel t b) := by ring
  have hI3 : Integrable (fun b => f b * normalizedKernel (V := V) t b) :=
    ((integrable_normalizedKernel (V := V) ht).const_mul M).mono'
      (hfm.mul hkm).aestronglyMeasurable (Filter.Eventually.of_forall fun b => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (normalizedKernel_pos ht b)]
        exact mul_le_mul_of_nonneg_right (hM b) (normalizedKernel_pos ht b).le)
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure V))
    hI1 hI2 hI3 (fun x _ => hf x) (fun x _ => (hdk x).differentiableAt)
  simp_rw [hdk'] at hibp
  have e : ∀ b, ⟪u, b⟫ * f b * normalizedKernel t b =
      (-2 * t)⁻¹ * (f b * (normalizedKernel t b * (-2 * t) * ⟪b, u⟫)) := by
    intro b; rw [real_inner_comm]; field_simp
  simp_rw [e]
  rw [integral_const_mul, hibp]
  have : (-2 * t)⁻¹ = -(2 * t)⁻¹ := by rw [neg_mul, inv_neg]
  rw [this]; ring


theorem measurable_clm_apply {α : Type*} [MeasurableSpace α] {φ : α → V →L[ℝ] ℝ} {v : α → V}
    (hφ : Measurable φ) (hv : Measurable v) : Measurable (fun a => φ a (v a)) :=
  (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := V) (F := ℝ)).continuous.measurable.comp (hφ.prodMk hv)

/-- the rotation path and its velocity -/
theorem hasDerivAt_rotPath {F : V → ℝ} (hF : Differentiable ℝ F) (x a a' : V) (θ : ℝ) :
    HasDerivAt (fun θ => F (x + Real.cos θ • a + Real.sin θ • a'))
      (fderiv ℝ F (x + Real.cos θ • a + Real.sin θ • a') (-Real.sin θ • a + Real.cos θ • a')) θ := by
  have hp : HasDerivAt (fun θ : ℝ => x + Real.cos θ • a + Real.sin θ • a')
      (-Real.sin θ • a + Real.cos θ • a') θ := by
    have h1 := (Real.hasDerivAt_cos θ).smul_const a
    have h2 := (Real.hasDerivAt_sin θ).smul_const a'
    exact (h1.const_add x).add h2
  exact (hF _).hasFDerivAt.comp_hasDerivAt θ hp

theorem norm_rot_vel_le (a a' : V) (θ : ℝ) : ‖-Real.sin θ • a + Real.cos θ • a'‖ ≤ ‖a‖ + ‖a'‖ := by
  calc ‖-Real.sin θ • a + Real.cos θ • a'‖ ≤ ‖-Real.sin θ • a‖ + ‖Real.cos θ • a'‖ := norm_add_le _ _
    _ = |Real.sin θ| * ‖a‖ + |Real.cos θ| * ‖a'‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
    _ ≤ 1 * ‖a‖ + 1 * ‖a'‖ := by
        gcongr
        · exact Real.abs_sin_le_one θ
        · exact Real.abs_cos_le_one θ
    _ = ‖a‖ + ‖a'‖ := by ring

theorem path_ftc {F : V → ℝ} (hF : Differentiable ℝ F) {L : ℝ} (hL : ∀ y, ‖fderiv ℝ F y‖ ≤ L)
    (x a a' : V) :
    F (x + a') - F (x + a) = ∫ θ in (0:ℝ)..(Real.pi / 2),
      fderiv ℝ F (x + Real.cos θ • a + Real.sin θ • a') (-Real.sin θ • a + Real.cos θ • a') := by
  have hL0 : 0 ≤ L := le_trans (norm_nonneg _) (hL 0)
  have hmeas : Measurable fun θ : ℝ =>
      fderiv ℝ F (x + Real.cos θ • a + Real.sin θ • a') (-Real.sin θ • a + Real.cos θ • a') :=
    measurable_clm_apply ((measurable_fderiv ℝ F).comp (by fun_prop)) (by fun_prop)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hasDerivAt_rotPath hF x a a' θ)]
  · simp
  · refine (intervalIntegrable_const (c := L * (‖a‖ + ‖a'‖))).mono_fun' hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun θ => ?_)
    simp only []
    calc ‖fderiv ℝ F (x + Real.cos θ • a + Real.sin θ • a') (-Real.sin θ • a + Real.cos θ • a')‖ ≤ ‖fderiv ℝ F (x + Real.cos θ • a + Real.sin θ • a')‖ *
          ‖-Real.sin θ • a + Real.cos θ • a'‖ := by
          exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ L * (‖a‖ + ‖a'‖) := mul_le_mul (hL _) (norm_rot_vel_le a a' θ) (norm_nonneg _) hL0


theorem gauss_abs_clm_le {t : ℝ} (ht : 0 < t) (ℓ : V →L[ℝ] ℝ) :
    ∫ b, |ℓ b| ∂(gaussianLaw t) ≤ ‖ℓ‖ * Real.sqrt (1 / (2 * t)) := by
  haveI := gaussianLaw_probability (V := V) ht
  set v := (InnerProductSpace.toDual ℝ V).symm ℓ
  have hv : ∀ b, ℓ b = ⟪v, b⟫ := fun b => by simp [v]
  have hnv : ‖v‖ = ‖ℓ‖ := by simp [v]
  simp_rw [hv]
  have hmem := memLp_inner_gaussian (V := V) ht v
  have h1 : (∫ b, |⟪v, b⟫| ∂(gaussianLaw t)) ^ 2 ≤ ∫ b, ⟪v, b⟫ ^ 2 ∂(gaussianLaw t) := by
    have := sq_integral_le_integral_sq hmem.abs
    simpa [sq_abs] using this
  rw [FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_inner_sq_readable ht v] at h1
  have h0 : 0 ≤ ∫ b, |⟪v, b⟫| ∂(gaussianLaw t) := integral_nonneg fun _ => abs_nonneg _
  rw [← hnv, ← Real.sqrt_sq (norm_nonneg v), ← Real.sqrt_mul (sq_nonneg _)]
  apply Real.le_sqrt_of_sq_le
  calc (∫ b, |⟪v, b⟫| ∂(gaussianLaw t)) ^ 2 ≤ ‖v‖ ^ 2 / (2 * t) := h1
    _ = ‖v‖ ^ 2 * (1 / (2 * t)) := by ring

variable [CompleteSpace V] [SecondCountableTopology V]

theorem rot_integral {t : ℝ} (ht : 0 < t) {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (Φ : V × V → ℝ)
    (hΦ : Measurable Φ) :
    ∫ p, Φ (rotCLM c s p) ∂((gaussianLaw t).prod (gaussianLaw t)) =
      ∫ p, Φ p ∂((gaussianLaw t).prod (gaussianLaw t)) := by
  rw [← integral_map (rotCLM c s).continuous.measurable.aemeasurable hΦ.aestronglyMeasurable,
    map_rot_gaussian ht c s hcs]

theorem integrable_norm_add_norm_gauss {t : ℝ} (ht : 0 < t) :
    Integrable (fun p : V × V => ‖p.1‖ + ‖p.2‖) ((gaussianLaw t).prod (gaussianLaw t)) := by
  haveI := gaussianLaw_probability (V := V) ht
  have h1 := (integrable_id_gaussian (V := V) ht).norm
  exact (h1.comp_fst (gaussianLaw t)).add (h1.comp_snd (gaussianLaw t))


/-- the integrand of the rotation argument -/
noncomputable def rotJ (F : V → ℝ) (x : V) (θ : ℝ) (p : V × V) : ℝ :=
  |fderiv ℝ F (x + (rotCLM (Real.cos θ) (Real.sin θ) p).1) (rotCLM (Real.cos θ) (Real.sin θ) p).2|

theorem measurable_rotJ (F : V → ℝ) (x : V) : Measurable (Function.uncurry fun p θ => rotJ F x θ p) := by
  unfold rotJ Function.uncurry
  simp only [rotCLM_apply]
  refine (measurable_clm_apply ((measurable_fderiv ℝ F).comp ?_) ?_).abs
  · fun_prop
  · fun_prop

theorem rotJ_le {F : V → ℝ} {L : ℝ} (hL : ∀ y, ‖fderiv ℝ F y‖ ≤ L) (x : V) (θ : ℝ) (p : V × V) :
    rotJ F x θ p ≤ L * (‖p.1‖ + ‖p.2‖) := by
  have hL0 : 0 ≤ L := le_trans (norm_nonneg _) (hL 0)
  unfold rotJ
  rw [rotCLM_apply, ← Real.norm_eq_abs]
  calc ‖fderiv ℝ F _ _‖ ≤ ‖fderiv ℝ F (x + (Real.cos θ • p.1 + Real.sin θ • p.2))‖ *
        ‖(-Real.sin θ) • p.1 + Real.cos θ • p.2‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ L * (‖p.1‖ + ‖p.2‖) := mul_le_mul (hL _) (norm_rot_vel_le p.1 p.2 θ) (norm_nonneg _) hL0

theorem abs_sub_le_rotJ {F : V → ℝ} (hF : Differentiable ℝ F) {L : ℝ}
    (hL : ∀ y, ‖fderiv ℝ F y‖ ≤ L) (x : V) (p : V × V) :
    |F (x + p.2) - F (x + p.1)| ≤ ∫ θ in Set.Ioc (0:ℝ) (Real.pi / 2), rotJ F x θ p := by
  have hpi : (0:ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  rw [path_ftc hF hL x p.1 p.2, ← intervalIntegral.integral_of_le hpi]
  refine (intervalIntegral.abs_integral_le_integral_abs hpi).trans (le_of_eq ?_)
  congr 1; funext θ
  unfold rotJ
  rw [rotCLM_apply, add_assoc]

theorem gauss_L1 {t : ℝ} (ht : 0 < t) {F : V → ℝ} (hF : Differentiable ℝ F) {M L : ℝ}
    (hM : ∀ y, |F y| ≤ M) (hL : ∀ y, ‖fderiv ℝ F y‖ ≤ L) (x : V) :
    ∫ a, |F (x + a) - heat t F x| ∂(gaussianLaw t) ≤
      Real.pi / 2 * Real.sqrt (1 / (2 * t)) * ∫ a, ‖fderiv ℝ F (x + a)‖ ∂(gaussianLaw t) := by
  haveI := gaussianLaw_probability (V := V) ht
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hL0 : 0 ≤ L := le_trans (norm_nonneg _) (hL 0)
  have hFc : Continuous F := hF.continuous
  set γ := gaussianLaw (V := V) t
  set ι := (volume : Measure ℝ).restrict (Set.Ioc 0 (Real.pi / 2))
  haveI : IsFiniteMeasure ι := by
    unfold ι; exact isFiniteMeasure_restrict.2 (by simp)
  have hFx : ∀ a : V, Integrable (fun a' => F (x + a')) γ := fun _ =>
    (integrable_const M).mono' (hFc.comp (by fun_prop)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun a' => by rw [Real.norm_eq_abs]; exact hM _)
  -- Step A
  have hA : ∀ a, |F (x + a) - heat t F x| ≤ ∫ a', |F (x + a') - F (x + a)| ∂γ := by
    intro a
    rw [heat_eq ht]
    have : F (x + a) - ∫ a', F (x + a') ∂γ = ∫ a', (F (x + a) - F (x + a')) ∂γ := by
      rw [integral_sub (integrable_const _) (hFx a)]; simp
    rw [this]
    refine (abs_integral_le_integral_abs).trans (le_of_eq ?_)
    congr 1; funext a'; exact abs_sub_comm _ _
  have hint2 : Integrable (fun p : V × V => |F (x + p.2) - F (x + p.1)|) (γ.prod γ) :=
    (integrable_const (2 * M)).mono' (by fun_prop) (Filter.Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs, abs_abs]
      calc |F (x + p.2) - F (x + p.1)| ≤ |F (x + p.2)| + |F (x + p.1)| := abs_sub _ _
        _ ≤ 2 * M := by linarith [hM (x + p.2), hM (x + p.1)])
  -- Step B
  have hB : ∫ a, ∫ a', |F (x + a') - F (x + a)| ∂γ ∂γ =
      ∫ p, |F (x + p.2) - F (x + p.1)| ∂(γ.prod γ) := (integral_prod _ hint2).symm
  -- integrability for the swap
  have hJm := measurable_rotJ F x
  have hJint : Integrable (Function.uncurry fun p θ => rotJ F x θ p) ((γ.prod γ).prod ι) := by
    have hb : Integrable (fun q : (V × V) × ℝ => L * (‖q.1.1‖ + ‖q.1.2‖)) ((γ.prod γ).prod ι) :=
      ((integrable_norm_add_norm_gauss (V := V) ht).comp_fst ι).const_mul L
    refine hb.mono' hJm.aestronglyMeasurable (Filter.Eventually.of_forall fun q => ?_)
    show ‖rotJ F x q.2 q.1‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (by unfold rotJ; exact abs_nonneg _)]
    exact rotJ_le hL x q.2 q.1
  -- Step C
  have hC : ∫ p, |F (x + p.2) - F (x + p.1)| ∂(γ.prod γ) ≤
      ∫ p, ∫ θ, rotJ F x θ p ∂ι ∂(γ.prod γ) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      hJint.integral_prod_left (Filter.Eventually.of_forall fun p => abs_sub_le_rotJ hF hL x p)
  -- Step D/E
  set K := ∫ p, |fderiv ℝ F (x + p.1) p.2| ∂(γ.prod γ)
  have hE : ∀ θ, ∫ p, rotJ F x θ p ∂(γ.prod γ) = K := by
    intro θ
    exact rot_integral ht (by rw [add_comm]; exact Real.sin_sq_add_cos_sq θ)
      (fun p => |fderiv ℝ F (x + p.1) p.2|)
      (measurable_clm_apply ((measurable_fderiv ℝ F).comp (by fun_prop)) measurable_snd).abs
  have hD : ∫ p, ∫ θ, rotJ F x θ p ∂ι ∂(γ.prod γ) = ∫ θ, ∫ p, rotJ F x θ p ∂(γ.prod γ) ∂ι :=
    integral_integral_swap hJint
  -- Step F
  have hKint : Integrable (fun p : V × V => |fderiv ℝ F (x + p.1) p.2|) (γ.prod γ) := by
    refine ((integrable_norm_add_norm_gauss (V := V) ht).const_mul L).mono'
      (measurable_clm_apply ((measurable_fderiv ℝ F).comp (by fun_prop)) measurable_snd).abs.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_abs]
    calc |fderiv ℝ F (x + p.1) p.2| ≤ ‖fderiv ℝ F (x + p.1)‖ * ‖p.2‖ := by
          rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ L * (‖p.1‖ + ‖p.2‖) := mul_le_mul (hL _) (by linarith [norm_nonneg p.1]) (norm_nonneg _) hL0
  have hpt : ∀ a, ∫ b, |fderiv ℝ F (x + a) b| ∂γ ≤ ‖fderiv ℝ F (x + a)‖ * Real.sqrt (1 / (2 * t)) :=
    fun a => gauss_abs_clm_le ht _
  have hF : K ≤ Real.sqrt (1 / (2 * t)) * ∫ a, ‖fderiv ℝ F (x + a)‖ ∂γ := by
    unfold K
    rw [integral_prod _ hKint]
    simp only []
    calc ∫ a, ∫ b, |fderiv ℝ F (x + a) b| ∂γ ∂γ ≤ ∫ a, ‖fderiv ℝ F (x + a)‖ * Real.sqrt (1 / (2 * t)) ∂γ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => integral_nonneg fun _ => abs_nonneg _)
            (((integrable_const L).mono' ((measurable_fderiv ℝ F).comp (by fun_prop)).norm.aestronglyMeasurable
              (Filter.Eventually.of_forall fun a => by rw [norm_norm]; exact hL _)).mul_const _)
            (Filter.Eventually.of_forall hpt)
      _ = _ := by rw [integral_mul_const, mul_comm]
  -- assemble
  have hι : ι.real Set.univ = Real.pi / 2 := by
    unfold ι
    rw [Measure.real, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Ioc,
      sub_zero, ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  calc ∫ a, |F (x + a) - heat t F x| ∂γ ≤ ∫ a, ∫ a', |F (x + a') - F (x + a)| ∂γ ∂γ := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
          hint2.integral_prod_left
          (Filter.Eventually.of_forall hA)
    _ = ∫ p, |F (x + p.2) - F (x + p.1)| ∂(γ.prod γ) := hB
    _ ≤ ∫ p, ∫ θ, rotJ F x θ p ∂ι ∂(γ.prod γ) := hC
    _ = ∫ θ, ∫ p, rotJ F x θ p ∂(γ.prod γ) ∂ι := hD
    _ = ∫ θ, K ∂ι := by congr 1; funext θ; exact hE θ
    _ = Real.pi / 2 * K := by rw [integral_const, smul_eq_mul, hι]
    _ ≤ Real.pi / 2 * (Real.sqrt (1 / (2 * t)) * ∫ a, ‖fderiv ℝ F (x + a)‖ ∂γ) :=
        mul_le_mul_of_nonneg_left hF (by positivity)
    _ = _ := by ring


/-- the integrand of the covariance argument -/
noncomputable def rotC (G F : V → ℝ) (x : V) (θ : ℝ) (p : V × V) : ℝ :=
  G (x + p.1) * fderiv ℝ F (x + (rotCLM (Real.cos θ) (Real.sin θ) p).1)
    (rotCLM (Real.cos θ) (Real.sin θ) p).2

theorem stein_shift {t : ℝ} (ht : 0 < t) {G : V → ℝ} (hG : Differentiable ℝ G) {MG LG : ℝ}
    (hMG : ∀ y, |G y| ≤ MG) (hLG : ∀ y, ‖fderiv ℝ G y‖ ≤ LG) (z u : V) {σ : ℝ} (hσ : 0 ≤ σ) :
    |∫ b, G (z - σ • b) * ⟪u, b⟫ ∂(gaussianLaw t)| ≤ (2 * t)⁻¹ * σ * LG * ‖u‖ := by
  have hLG0 : 0 ≤ LG := le_trans (norm_nonneg _) (hLG 0)
  haveI := gaussianLaw_probability (V := V) ht
  set f : V → ℝ := fun b => G (z - σ • b)
  have hfd : ∀ b, HasFDerivAt f ((fderiv ℝ G (z - σ • b)).comp (-σ • ContinuousLinearMap.id ℝ V)) b := by
    intro b
    have h1 : HasFDerivAt (fun b : V => z - σ • b) (-σ • ContinuousLinearMap.id ℝ V) b := by
      have := ((hasFDerivAt_id (𝕜 := ℝ) b).const_smul σ).const_sub z
      convert this using 1
      · rfl
      · rw [neg_smul]
    exact (hG _).hasFDerivAt.comp b h1
  have hfdiff : Differentiable ℝ f := fun b => (hfd b).differentiableAt
  have hfL : ∀ b, ‖fderiv ℝ f b‖ ≤ σ * LG := by
    intro b
    rw [(hfd b).fderiv]
    calc ‖(fderiv ℝ G (z - σ • b)).comp (-σ • ContinuousLinearMap.id ℝ V)‖
        ≤ ‖fderiv ℝ G (z - σ • b)‖ * ‖-σ • ContinuousLinearMap.id ℝ V‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ LG * σ := by
          apply mul_le_mul (hLG _) _ (norm_nonneg _) hLG0
          refine (norm_smul_le (-σ) (ContinuousLinearMap.id ℝ V)).trans ?_
          rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg hσ]
          exact mul_le_of_le_one_right hσ ContinuousLinearMap.norm_id_le
      _ = σ * LG := by ring
  have hst := stein ht hfdiff (fun b => hMG _) hfL u
  have e : ∫ b, G (z - σ • b) * ⟪u, b⟫ ∂(gaussianLaw t) = ∫ b, ⟪u, b⟫ * f b ∂(gaussianLaw t) := by
    congr 1; funext b; ring
  rw [e, hst, abs_mul, abs_of_pos (by positivity : (0:ℝ) < (2 * t)⁻¹)]
  have hb : ∀ b, |fderiv ℝ f b u| ≤ σ * LG * ‖u‖ := by
    intro b
    rw [← Real.norm_eq_abs]
    exact ((fderiv ℝ f b).le_opNorm u).trans (mul_le_mul_of_nonneg_right (hfL b) (norm_nonneg _))
  calc (2 * t)⁻¹ * |∫ b, fderiv ℝ f b u ∂(gaussianLaw t)|
      ≤ (2 * t)⁻¹ * ∫ _b, σ * LG * ‖u‖ ∂(gaussianLaw t) := by
        gcongr
        refine abs_integral_le_integral_abs.trans ?_
        exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
          (integrable_const _) (Filter.Eventually.of_forall hb)
    _ = _ := by simp; ring


theorem gauss_cov {t : ℝ} (ht : 0 < t) {G F : V → ℝ} (hG : Differentiable ℝ G) {MG LG : ℝ}
    (hMG : ∀ y, |G y| ≤ MG) (hLG : ∀ y, ‖fderiv ℝ G y‖ ≤ LG) (hF : Differentiable ℝ F) {M L : ℝ}
    (hM : ∀ y, |F y| ≤ M) (hL : ∀ y, ‖fderiv ℝ F y‖ ≤ L) (x : V) :
    |heat t (fun y => G y * F y) x - heat t G x * heat t F x| ≤
      (2 * t)⁻¹ * LG * ∫ a, ‖fderiv ℝ F (x + a)‖ ∂(gaussianLaw t) := by
  haveI := gaussianLaw_probability (V := V) ht
  have hMG0 : 0 ≤ MG := le_trans (abs_nonneg _) (hMG 0)
  have hLG0 : 0 ≤ LG := le_trans (norm_nonneg _) (hLG 0)
  have hL0 : 0 ≤ L := le_trans (norm_nonneg _) (hL 0)
  have hGc : Continuous G := hG.continuous
  have hFc : Continuous F := hF.continuous
  set γ := gaussianLaw (V := V) t
  set ι := (volume : Measure ℝ).restrict (Set.Ioc 0 (Real.pi / 2))
  haveI : IsFiniteMeasure ι := by
    unfold ι; exact isFiniteMeasure_restrict.2 (by simp)
  have hpi : (0:ℝ) ≤ Real.pi / 2 := by linarith [Real.pi_pos]
  have hbG : ∀ a : V, Integrable (fun a' => G (x + a')) γ := fun _ =>
    (integrable_const MG).mono' (hGc.comp (by fun_prop)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun a' => by rw [Real.norm_eq_abs]; exact hMG _)
  have hbF : Integrable (fun a' => F (x + a')) γ :=
    (integrable_const M).mono' (hFc.comp (by fun_prop)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun a' => by rw [Real.norm_eq_abs]; exact hM _)
  -- Step 1
  have hcov : heat t (fun y => G y * F y) x - heat t G x * heat t F x =
      -(∫ p, G (x + p.1) * (F (x + p.2) - F (x + p.1)) ∂(γ.prod γ)) := by
    rw [heat_eq ht, heat_eq ht, heat_eq ht]
    have h1 : ∫ p, G (x + p.1) * F (x + p.2) ∂(γ.prod γ) = (∫ a, G (x + a) ∂γ) * ∫ a, F (x + a) ∂γ :=
      integral_prod_mul (fun a => G (x + a)) (fun a => F (x + a))
    have h2 : ∫ p, G (x + p.1) * F (x + p.1) ∂(γ.prod γ) = ∫ a, G (x + a) * F (x + a) ∂γ := by
      rw [integral_prod]
      · simp
      · exact (integrable_const (MG * M)).mono' (by fun_prop) (Filter.Eventually.of_forall fun p => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hMG _) (hM _) (abs_nonneg _) hMG0)
    have hi1 : Integrable (fun p : V × V => G (x + p.1) * F (x + p.2)) (γ.prod γ) :=
      (integrable_const (MG * M)).mono' (by fun_prop) (Filter.Eventually.of_forall fun p => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hMG _) (hM _) (abs_nonneg _) hMG0)
    have hi2 : Integrable (fun p : V × V => G (x + p.1) * F (x + p.1)) (γ.prod γ) :=
      (integrable_const (MG * M)).mono' (by fun_prop) (Filter.Eventually.of_forall fun p => by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hMG _) (hM _) (abs_nonneg _) hMG0)
    simp_rw [mul_sub]
    rw [integral_sub hi1 hi2, h1, h2]
    ring
  -- Step 2
  have hrotC_meas : Measurable (Function.uncurry fun p θ => rotC G F x θ p) := by
    unfold rotC Function.uncurry
    simp only [rotCLM_apply]
    exact (hGc.measurable.comp (by fun_prop)).mul
      (measurable_clm_apply ((measurable_fderiv ℝ F).comp (by fun_prop)) (by fun_prop))
  have hrotC_le : ∀ θ p, |rotC G F x θ p| ≤ MG * (L * (‖p.1‖ + ‖p.2‖)) := by
    intro θ p
    unfold rotC
    rw [abs_mul]
    apply mul_le_mul (hMG _) _ (abs_nonneg _) hMG0
    have := rotJ_le hL x θ p
    unfold rotJ at this
    exact this
  have hJint : Integrable (Function.uncurry fun p θ => rotC G F x θ p) ((γ.prod γ).prod ι) := by
    have hb : Integrable (fun q : (V × V) × ℝ => MG * (L * (‖q.1.1‖ + ‖q.1.2‖))) ((γ.prod γ).prod ι) :=
      (((integrable_norm_add_norm_gauss (V := V) ht).comp_fst ι).const_mul L).const_mul MG
    refine hb.mono' hrotC_meas.aestronglyMeasurable (Filter.Eventually.of_forall fun q => ?_)
    rw [Real.norm_eq_abs]
    exact hrotC_le q.2 q.1
  have hstep2 : ∀ p : V × V, G (x + p.1) * (F (x + p.2) - F (x + p.1)) =
      ∫ θ, rotC G F x θ p ∂ι := by
    intro p
    rw [path_ftc hF hL x p.1 p.2, intervalIntegral.integral_of_le hpi, ← integral_const_mul]
    congr 1; funext θ
    unfold rotC
    rw [rotCLM_apply, add_assoc]
  -- Step 4,5
  set A := ∫ a, ‖fderiv ℝ F (x + a)‖ ∂γ
  have hstep5 : ∀ θ ∈ Set.Ioc (0:ℝ) (Real.pi / 2),
      |∫ p, rotC G F x θ p ∂(γ.prod γ)| ≤ (2 * t)⁻¹ * Real.sin θ * LG * A := by
    intro θ hθ
    have hsin : 0 ≤ Real.sin θ :=
      Real.sin_nonneg_of_nonneg_of_le_pi hθ.1.le (by linarith [hθ.2, Real.pi_pos])
    set c := Real.cos θ
    set σ := Real.sin θ
    have hcs : c ^ 2 + σ ^ 2 = 1 := by rw [add_comm]; exact Real.sin_sq_add_cos_sq θ
    set Ψ : V × V → ℝ := fun q => G (x + (c • q.1 - σ • q.2)) * fderiv ℝ F (x + q.1) q.2
    have hΨm : Measurable Ψ :=
      (hGc.measurable.comp (by fun_prop)).mul
        (measurable_clm_apply ((measurable_fderiv ℝ F).comp (by fun_prop)) measurable_snd)
    have hΨR : ∀ p, Ψ (rotCLM c σ p) = rotC G F x θ p := by
      intro p
      simp only [Ψ, rotC, rotCLM_apply]
      congr 3
      have : c • (c • p.1 + σ • p.2) - σ • ((-σ) • p.1 + c • p.2) = (c ^ 2 + σ ^ 2) • p.1 := by
        simp only [smul_add, smul_smul, neg_smul, smul_neg, sub_neg_eq_add, add_smul]
        rw [mul_comm σ c]; abel_nf
        rw [sq, sq]
      rw [this, hcs, one_smul]
    have hrot := rot_integral ht hcs Ψ hΨm
    simp_rw [hΨR] at hrot
    rw [hrot]
    have hΨint : Integrable Ψ (γ.prod γ) := by
      refine (((integrable_norm_add_norm_gauss (V := V) ht).const_mul L).const_mul MG).mono'
        hΨm.aestronglyMeasurable (Filter.Eventually.of_forall fun q => ?_)
      simp only [Ψ, Real.norm_eq_abs, abs_mul]
      apply mul_le_mul (hMG _) _ (abs_nonneg _) hMG0
      rw [← Real.norm_eq_abs]
      calc ‖fderiv ℝ F (x + q.1) q.2‖ ≤ ‖fderiv ℝ F (x + q.1)‖ * ‖q.2‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ L * (‖q.1‖ + ‖q.2‖) := mul_le_mul (hL _) (by linarith [norm_nonneg q.1]) (norm_nonneg _) hL0
    rw [integral_prod _ hΨint]
    have hinner : ∀ a : V, |∫ b, Ψ (a, b) ∂γ| ≤ (2 * t)⁻¹ * σ * LG * ‖fderiv ℝ F (x + a)‖ := by
      intro a
      set u := (InnerProductSpace.toDual ℝ V).symm (fderiv ℝ F (x + a))
      have hu : ∀ b, fderiv ℝ F (x + a) b = ⟪u, b⟫ := fun b => by simp [u]
      have hnu : ‖u‖ = ‖fderiv ℝ F (x + a)‖ := by simp [u]
      have e : ∀ b, Ψ (a, b) = G ((x + c • a) - σ • b) * ⟪u, b⟫ := by
        intro b; simp only [Ψ]; rw [hu]; congr 2; abel
      simp_rw [e]
      rw [← hnu]
      exact stein_shift ht hG hMG hLG (x + c • a) u hsin
    calc |∫ a, ∫ b, Ψ (a, b) ∂γ ∂γ| ≤ ∫ a, |∫ b, Ψ (a, b) ∂γ| ∂γ := abs_integral_le_integral_abs
      _ ≤ ∫ a, (2 * t)⁻¹ * σ * LG * ‖fderiv ℝ F (x + a)‖ ∂γ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
            (((integrable_const L).mono' ((measurable_fderiv ℝ F).comp (by fun_prop)).norm.aestronglyMeasurable
              (Filter.Eventually.of_forall fun a => by rw [norm_norm]; exact hL _)).const_mul _)
            (Filter.Eventually.of_forall hinner)
      _ = (2 * t)⁻¹ * σ * LG * A := by rw [integral_const_mul]
  -- assemble
  rw [hcov]
  simp_rw [hstep2]
  rw [abs_neg, integral_integral_swap hJint]
  have hsinint : ∫ θ, Real.sin θ ∂ι = 1 := by
    unfold ι
    rw [← intervalIntegral.integral_of_le hpi, integral_sin]
    simp
  calc |∫ θ, ∫ p, rotC G F x θ p ∂(γ.prod γ) ∂ι| ≤ ∫ θ, |∫ p, rotC G F x θ p ∂(γ.prod γ)| ∂ι :=
        abs_integral_le_integral_abs
    _ ≤ ∫ θ, (2 * t)⁻¹ * Real.sin θ * LG * A ∂ι := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
        · exact (((Real.continuous_sin.integrableOn_Icc (a := 0) (b := Real.pi / 2)).mono_set
            Set.Ioc_subset_Icc_self).const_mul ((2 * t)⁻¹)).mul_const _ |>.mul_const _
        · unfold ι
          rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
          exact Filter.Eventually.of_forall hstep5
    _ = (2 * t)⁻¹ * LG * A := by
        have : (fun θ => (2 * t)⁻¹ * Real.sin θ * LG * A) = fun θ => ((2 * t)⁻¹ * LG * A) * Real.sin θ := by
          funext θ; ring
        rw [this, integral_const_mul, hsinint, mul_one]

end KB


-- ===== from Solutions/KB/Ledoux.lean =====

open MeasureTheory ProbabilityTheory
open FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
open scoped RealInnerProductSpace

namespace KB
variable {n : ℕ} (ν : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ν]
variable {t : ℝ} (ht : 0 < t)

/-- the stationary measure of the chain -/
noncomputable def chainM (ν : Measure (EuclideanSpace ℝ (Fin n))) (t : ℝ) :
    Measure (EuclideanSpace ℝ (Fin n)) := ν.conv (gaussianLaw t)

include ht

theorem chainM_isProb : IsProbabilityMeasure (chainM ν t) := by
  haveI := gaussianLaw_probability (V := EuclideanSpace ℝ (Fin n)) ht
  unfold chainM; infer_instance

theorem heat_one (x : EuclideanSpace ℝ (Fin n)) : heat t (fun _ => (1:ℝ)) x = 1 := heat_const ht 1 x

theorem int_chainM {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : BM f) :
    ∫ y, f y ∂(chainM ν t) = ∫ x, heat t f x ∂ν := integral_conv_gaussian ν ht hf

theorem int_mul_Kc {g f : EuclideanSpace ℝ (Fin n) → ℝ} (hg : BM g) (hf : BM f) :
    ∫ y, g y * Kc t ν f y ∂(chainM ν t) = ∫ x, heat t g x * heat t f x ∂ν :=
  bayes ν ht hg (heat_BM ht hf)

theorem Kc_selfadj {g f : EuclideanSpace ℝ (Fin n) → ℝ} (hg : BM g) (hf : BM f) :
    ∫ y, g y * Kc t ν f y ∂(chainM ν t) = ∫ y, Kc t ν g y * f y ∂(chainM ν t) := by
  rw [int_mul_Kc ν ht hg hf]
  have := int_mul_Kc ν ht hf hg
  rw [show (fun y => Kc t ν g y * f y) = fun y => f y * Kc t ν g y by funext y; ring, this]
  congr 1; funext x; ring

theorem iterate_selfadj {g f : EuclideanSpace ℝ (Fin n) → ℝ} (hg : BM g) (hf : BM f) (j : ℕ) :
    ∫ y, g y * (Kc t ν)^[j] f y ∂(chainM ν t) = ∫ y, (Kc t ν)^[j] g y * f y ∂(chainM ν t) := by
  induction j generalizing g with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply', Kc_selfadj ν ht hg (iterate_BM ν ht hf j),
      ih (Kc_BM ν ht hg), Function.iterate_succ_apply]

theorem int_Kc {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : BM f) :
    ∫ y, Kc t ν f y ∂(chainM ν t) = ∫ y, f y ∂(chainM ν t) := by
  have h1 : BM (fun _ : EuclideanSpace ℝ (Fin n) => (1:ℝ)) := ⟨measurable_const, 1, fun _ => by simp⟩
  have := int_mul_Kc ν ht h1 hf
  simp only [one_mul] at this
  rw [this, int_chainM ν ht hf]
  congr 1; funext x; rw [heat_one ht, one_mul]

theorem int_iterate {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : BM f) (j : ℕ) :
    ∫ y, (Kc t ν)^[j] f y ∂(chainM ν t) = ∫ y, f y ∂(chainM ν t) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', int_Kc ν ht (iterate_BM ν ht hf j), ih]


theorem post_sq_le {w : EuclideanSpace ℝ (Fin n) → ℝ} (hw : BM w) (y : EuclideanSpace ℝ (Fin n)) :
    post t ν w y ^ 2 ≤ post t ν (fun x => w x ^ 2) y := by
  haveI := postMeasure_isProb ν ht y
  rw [post_eq_integral ν ht, post_eq_integral ν ht]
  obtain ⟨hm, M, hM⟩ := hw
  exact sq_integral_le_integral_sq (MemLp.of_bound hm.aestronglyMeasurable M
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hM x))

theorem int_sq_Kc_le {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : BM u) :
    ∫ y, Kc t ν u y ^ 2 ∂(chainM ν t) ≤ ∫ x, heat t u x ^ 2 ∂ν := by
  haveI := chainM_isProb ν ht
  have hH := heat_BM ht hu
  have hH2 := BM.sq hH
  have h1 : BM (fun _ : EuclideanSpace ℝ (Fin n) => (1:ℝ)) := ⟨measurable_const, 1, fun _ => by simp⟩
  have hpost := post_BM ν ht hH2
  calc ∫ y, Kc t ν u y ^ 2 ∂(chainM ν t) ≤ ∫ y, post t ν (fun x => heat t u x ^ 2) y ∂(chainM ν t) := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _)
          hpost.integrable (Filter.Eventually.of_forall fun y => post_sq_le ν ht hH y)
    _ = ∫ x, heat t u x ^ 2 ∂ν := by
        have := bayes ν ht h1 hH2
        simp only [one_mul] at this
        unfold chainM
        rw [this]; congr 1; funext x; rw [heat_one ht, one_mul]

/-- spectral gap of the chain from a Poincaré inequality for the prior -/
theorem gap {P : ℝ} (hP0 : 0 ≤ P)
    (hP : ∀ g : EuclideanSpace ℝ (Fin n) → ℝ, BM g → Differentiable ℝ g →
      (∃ L, ∀ x, ‖fderiv ℝ g x‖ ≤ L) → variance g ν ≤ P * ∫ x, ‖fderiv ℝ g x‖ ^ 2 ∂ν)
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : BM u) (hmean : ∫ y, u y ∂(chainM ν t) = 0) :
    ∫ y, Kc t ν u y ^ 2 ∂(chainM ν t) ≤
      (2 * t * P / (1 + 2 * t * P)) * ∫ y, u y ^ 2 ∂(chainM ν t) := by
  haveI := chainM_isProb ν ht
  obtain ⟨hum, M, hM⟩ := hu
  have hu : BM u := ⟨hum, M, hM⟩
  have hH := heat_BM ht hu
  set Q := ∫ x, heat t u x ^ 2 ∂ν
  have hmeanH : ∫ x, heat t u x ∂ν = 0 := by rw [← int_chainM ν ht hu]; exact hmean
  have hdiff : Differentiable ℝ (heat t u) := fun x => (hasFDerivAt_heat' ht hum hM x).differentiableAt
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0)
  have hgradb : ∀ x, ‖fderiv ℝ (heat t u) x‖ ^ 2 ≤ 2 * t * (heat t (fun y => u y ^ 2) x - heat t u x ^ 2) :=
    fun x => norm_fderiv_heat_sq_le ht hum hM x
  have hLb : ∀ x, ‖fderiv ℝ (heat t u) x‖ ≤ Real.sqrt (2 * t) * M := by
    intro x
    have h2 := heat_abs_le ht (h := fun y => u y ^ 2) (M := M ^ 2) (fun y => by
      rw [abs_of_nonneg (sq_nonneg _)]
      have := hM y
      nlinarith [abs_nonneg (u y), sq_abs (u y)]) x
    have h3 : ‖fderiv ℝ (heat t u) x‖ ^ 2 ≤ (Real.sqrt (2 * t) * M) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by linarith)]
      nlinarith [hgradb x, le_abs_self (heat t (fun y => u y ^ 2) x), sq_nonneg (heat t u x)]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).1 h3
  have hvar := hP (heat t u) hH hdiff ⟨_, hLb⟩
  have hmem : MemLp (heat t u) 2 ν := MemLp.of_bound hH.1.aestronglyMeasurable hH.2.choose
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hH.2.choose_spec x)
  rw [variance_eq_sub hmem, hmeanH] at hvar
  simp only [Pi.pow_apply] at hvar
  have hu2 : BM (fun y => u y ^ 2) := BM.sq hu
  have hint_grad : ∫ x, ‖fderiv ℝ (heat t u) x‖ ^ 2 ∂ν ≤ 2 * t * (∫ y, u y ^ 2 ∂(chainM ν t) - Q) := by
    rw [int_chainM ν ht hu2, ← integral_sub (heat_BM ht hu2).integrable (BM.sq hH).integrable,
      ← integral_const_mul]
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      ((((heat_BM ht hu2).add ((BM.sq hH).const_mul (-1))).const_mul (2 * t)).integrable |>
        fun h => by convert h using 2 with x; ring)
      (Filter.Eventually.of_forall hgradb)
  have hQ : Q ≤ P * (2 * t * (∫ y, u y ^ 2 ∂(chainM ν t) - Q)) := by
    have := mul_le_mul_of_nonneg_left hint_grad hP0
    simp at hvar
    linarith
  have hden : 0 < 1 + 2 * t * P := by positivity
  calc ∫ y, Kc t ν u y ^ 2 ∂(chainM ν t) ≤ Q := int_sq_Kc_le ν ht hu
    _ ≤ (2 * t * P / (1 + 2 * t * P)) * ∫ y, u y ^ 2 ∂(chainM ν t) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hden]
        nlinarith [hQ]


section Gap
variable {P : ℝ} (hP0 : 0 ≤ P)
    (hP : ∀ g : EuclideanSpace ℝ (Fin n) → ℝ, BM g → Differentiable ℝ g →
      (∃ L, ∀ x, ‖fderiv ℝ g x‖ ≤ L) → variance g ν ≤ P * ∫ x, ‖fderiv ℝ g x‖ ^ 2 ∂ν)
include hP0 hP

theorem iterate_gap {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : BM u)
    (hmean : ∫ y, u y ∂(chainM ν t) = 0) (k : ℕ) :
    ∫ y, (Kc t ν)^[k] u y ^ 2 ∂(chainM ν t) ≤
      (2 * t * P / (1 + 2 * t * P)) ^ k * ∫ y, u y ^ 2 ∂(chainM ν t) := by
  have hq0 : 0 ≤ 2 * t * P / (1 + 2 * t * P) := by positivity
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have hk := iterate_BM ν ht hu k
    have hmk : ∫ y, (Kc t ν)^[k] u y ∂(chainM ν t) = 0 := by rw [int_iterate ν ht hu k]; exact hmean
    calc ∫ y, Kc t ν ((Kc t ν)^[k] u) y ^ 2 ∂(chainM ν t)
        ≤ (2 * t * P / (1 + 2 * t * P)) * ∫ y, (Kc t ν)^[k] u y ^ 2 ∂(chainM ν t) :=
          gap ν ht hP0 hP hk hmk
      _ ≤ (2 * t * P / (1 + 2 * t * P)) *
            ((2 * t * P / (1 + 2 * t * P)) ^ k * ∫ y, u y ^ 2 ∂(chainM ν t)) :=
          mul_le_mul_of_nonneg_left ih hq0
      _ = _ := by ring

theorem upper_selfcorr {u : EuclideanSpace ℝ (Fin n) → ℝ} (hu : BM u) (k : ℕ) :
    ∫ y, u y * (Kc t ν)^[2 * k] u y ∂(chainM ν t) ≤
      (∫ y, u y ∂(chainM ν t)) ^ 2 + (2 * t * P / (1 + 2 * t * P)) ^ k *
        (∫ y, u y ^ 2 ∂(chainM ν t) - (∫ y, u y ∂(chainM ν t)) ^ 2) := by
  haveI := chainM_isProb ν ht
  set a := ∫ y, u y ∂(chainM ν t)
  have hk := iterate_BM ν ht hu k
  have e1 : ∫ y, u y * (Kc t ν)^[2 * k] u y ∂(chainM ν t) =
      ∫ y, (Kc t ν)^[k] u y ^ 2 ∂(chainM ν t) := by
    rw [show 2 * k = k + k by ring, Function.iterate_add_apply, iterate_selfadj ν ht hu hk k]
    congr 1; funext y; ring
  have hc : BM (fun _ : EuclideanSpace ℝ (Fin n) => a) := ⟨measurable_const, |a|, fun _ => le_rfl⟩
  have hw : BM (fun y => u y - a) := by
    have := hu.add (hc.const_mul (-1)); convert this using 2 with y; ring
  set w := (Kc t ν)^[k] (fun y => u y - a)
  have hwBM : BM w := iterate_BM ν ht hw k
  have hsplit : ∀ y, (Kc t ν)^[k] u y = w y + a := by
    intro y
    have := congrFun (iterate_sub ν ht hu hc k) y
    simp only [iterate_const ν ht] at this
    simp only [w]; rw [this]; ring
  have hmw : ∫ y, (u y - a) ∂(chainM ν t) = 0 := by
    rw [integral_sub hu.integrable (integrable_const a)]; simp [a]
  have hwm : ∫ y, w y ∂(chainM ν t) = 0 := by rw [int_iterate ν ht hw k]; exact hmw
  have hgap := iterate_gap ν ht hP0 hP hw hmw k
  have hvar : ∫ y, (u y - a) ^ 2 ∂(chainM ν t) = ∫ y, u y ^ 2 ∂(chainM ν t) - a ^ 2 := by
    have e : (fun y => (u y - a) ^ 2) = fun y => u y ^ 2 + ((-2 * a) * u y + a ^ 2) := by
      funext y; ring
    have hI : Integrable (fun y => (-2 * a) * u y + a ^ 2) (chainM ν t) :=
      (hu.integrable.const_mul _).add (integrable_const _)
    have hI2 : Integrable (fun y => (-2 * a) * u y) (chainM ν t) := hu.integrable.const_mul _
    rw [e, integral_add (BM.sq hu).integrable hI, integral_add hI2 (integrable_const _),
      integral_const_mul]
    simp [a]; ring
  rw [e1]
  simp_rw [hsplit]
  have e2 : (fun y => (w y + a) ^ 2) = fun y => w y ^ 2 + ((2 * a) * w y + a ^ 2) := by
    funext y; ring
  have hJ : Integrable (fun y => (2 * a) * w y + a ^ 2) (chainM ν t) :=
    (hwBM.integrable.const_mul _).add (integrable_const _)
  have hJ2 : Integrable (fun y => (2 * a) * w y) (chainM ν t) := hwBM.integrable.const_mul _
  rw [e2, integral_add (BM.sq hwBM).integrable hJ, integral_add hJ2 (integrable_const _),
    integral_const_mul, hwm]
  simp only [mul_zero, zero_add, integral_const, probReal_univ, smul_eq_mul, one_mul]
  rw [← hvar]
  linarith

end Gap


omit ht in
theorem sum_inv_sqrt_le (N : ℕ) :
    ∑ i ∈ Finset.range N, (if i = 0 then Real.pi / 2 else 1 / Real.sqrt i) ≤
      Real.pi / 2 + 3 * Real.sqrt N := by
  induction N with
  | zero => simp <;> positivity
  | succ N ih =>
    rw [Finset.sum_range_succ]
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp <;> positivity
    · rw [if_neg (by omega)]
      have hN' : (0:ℝ) < N := by exact_mod_cast hN
      have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
      have key : 1 / Real.sqrt N ≤ 3 * Real.sqrt ((N:ℝ) + 1) - 3 * Real.sqrt N := by
        have hs := Real.sqrt_pos.2 hN'
        rw [div_le_iff₀ hs]
        have e1 := Real.sq_sqrt hN'.le
        have hprod : Real.sqrt ((N:ℝ) + 1) * Real.sqrt N = Real.sqrt (((N:ℝ) + 1) * N) := by
          rw [← Real.sqrt_mul (by linarith)]
        have hge : (N:ℝ) + 1 / 3 ≤ Real.sqrt (((N:ℝ) + 1) * N) := by
          apply Real.le_sqrt_of_sq_le
          nlinarith
        nlinarith
      push_cast
      linarith

omit ht in
theorem abs_int_le_int {μ : Measure (EuclideanSpace ℝ (Fin n))} [IsFiniteMeasure μ]
    {f g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Integrable g μ) (h : ∀ x, |f x| ≤ g x) :
    |∫ x, f x ∂μ| ≤ ∫ x, g x ∂μ :=
  abs_integral_le_integral_abs.trans (integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun _ => abs_nonneg _) hg (Filter.Eventually.of_forall h))

/-- one term of the Ledoux sum -/
theorem ledoux_term (hν : PhiSobBayes.IsLogConcave ν) {u F : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : BM u) (hu1 : ∀ y, |u y| ≤ 1) (hF : BM F) (hFd : Differentiable ℝ F) {LF : ℝ}
    (hLF : ∀ y, ‖fderiv ℝ F y‖ ≤ LF) (i : ℕ) :
    |∫ y, (Kc t ν)^[i] u y * (F y - Kc t ν F y) ∂(chainM ν t)| ≤
      Real.sqrt (1 / (2 * t)) * (if i = 0 then Real.pi / 2 else 1 / Real.sqrt i) *
        ∫ y, ‖fderiv ℝ F y‖ ∂(chainM ν t) := by
  haveI := chainM_isProb ν ht
  haveI := gaussianLaw_probability (V := EuclideanSpace ℝ (Fin n)) ht
  set G := (Kc t ν)^[i] u
  have hG : BM G := iterate_BM ν ht hu i
  have hGF : BM (fun y => G y * F y) := hG.mul hF
  have hKF := Kc_BM ν ht hF
  have hGb : ∀ y, |G y| ≤ 1 := iterate_abs_le ν ht hu1 i
  have hgradF : BM (fun y => ‖fderiv ℝ F y‖) :=
    ⟨(measurable_fderiv ℝ F).norm, LF, fun y => by rw [abs_norm]; exact hLF y⟩
  have hsplit : ∫ y, G y * (F y - Kc t ν F y) ∂(chainM ν t) =
      ∫ x, (heat t (fun y => G y * F y) x - heat t G x * heat t F x) ∂ν := by
    simp_rw [mul_sub]
    rw [integral_sub hGF.integrable (hG.mul hKF).integrable, int_chainM ν ht hGF,
      int_mul_Kc ν ht hG hF, integral_sub (heat_BM ht hGF).integrable
        ((heat_BM ht hG).mul (heat_BM ht hF)).integrable]
  rw [hsplit, int_chainM ν ht hgradF, ← integral_const_mul]
  apply abs_int_le_int ((heat_BM ht hgradF).integrable.const_mul _)
  intro x
  have hheat : heat t (fun y => ‖fderiv ℝ F y‖) x = ∫ a, ‖fderiv ℝ F (x + a)‖ ∂(gaussianLaw t) :=
    heat_eq ht _ x
  rw [hheat]
  obtain ⟨hFm, MF, hMF⟩ := hF
  by_cases hi : i = 0
  · -- L¹ term
    rw [if_pos hi]
    have hG0 : G = u := by simp [G, hi]
    have e : heat t (fun y => G y * F y) x - heat t G x * heat t F x =
        ∫ a, G (x + a) * (F (x + a) - heat t F x) ∂(gaussianLaw t) := by
      rw [heat_eq ht, heat_eq ht, heat_eq ht (h := F), ← integral_mul_const]
      rw [← integral_sub]
      · congr 1; funext a; ring
      · exact ((integrable_const (1 * MF)).mono' ((hG.1.mul hFm).comp (by fun_prop)).aestronglyMeasurable
            (Filter.Eventually.of_forall fun a => by
              rw [Real.norm_eq_abs, abs_mul]; exact mul_le_mul (hGb _) (hMF _) (abs_nonneg _) zero_le_one))
      · exact ((integrable_const 1).mono' (hG.1.comp (by fun_prop)).aestronglyMeasurable
            (Filter.Eventually.of_forall fun a => by rw [Real.norm_eq_abs]; exact hGb _)).mul_const _
    rw [e]
    have hL1 := gauss_L1 ht hFd hMF hLF x
    calc |∫ a, G (x + a) * (F (x + a) - heat t F x) ∂(gaussianLaw t)|
        ≤ ∫ a, |F (x + a) - heat t F x| ∂(gaussianLaw t) := by
          refine abs_int_le_int ?_ (fun a => ?_)
          · exact (integrable_const (2 * MF)).mono' ((hFm.comp (by fun_prop)).sub_const _).abs.aestronglyMeasurable
              (Filter.Eventually.of_forall fun a => by
                rw [Real.norm_eq_abs, abs_abs]
                have := heat_abs_le ht hMF x
                linarith [abs_sub (F (x + a)) (heat t F x), hMF (x + a)])
          · rw [abs_mul]
            exact mul_le_of_le_one_left (abs_nonneg _) (hGb _)
      _ ≤ Real.pi / 2 * Real.sqrt (1 / (2 * t)) * ∫ a, ‖fderiv ℝ F (x + a)‖ ∂(gaussianLaw t) := hL1
      _ = _ := by ring
  · -- covariance term
    rw [if_neg hi]
    have hipos : (0:ℝ) < i := by exact_mod_cast Nat.pos_of_ne_zero hi
    obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have hGd : Differentiable ℝ G := by
      simp only [G, Function.iterate_succ_apply']
      exact differentiable_Kc ν ht (iterate_BM ν ht hu i')
    have hbound := iterate_grad_bound ν ht hν (i' + 1) hu
    have hLG : ∀ y, ‖fderiv ℝ G y‖ ≤ Real.sqrt (2 * t / ((i' + 1 : ℕ) : ℝ)) := by
      intro y
      have h1 := hbound y
      have h2 : (Kc t ν)^[i' + 1] (fun x => u x ^ 2) y ≤ 1 := by
        have := iterate_abs_le ν ht (h := fun x => u x ^ 2) (M := 1) (fun x => by
          rw [abs_of_nonneg (sq_nonneg _)]
          have := hu1 x
          nlinarith [abs_nonneg (u x), sq_abs (u x)]) (i' + 1) y
        exact le_trans (le_abs_self _) this
      apply Real.le_sqrt_of_sq_le
      rw [le_div_iff₀ hipos]
      nlinarith [sq_nonneg ((Kc t ν)^[i' + 1] u y)]
    have hcov := gauss_cov ht hGd hGb hLG hFd hMF hLF x
    refine hcov.trans (le_of_eq ?_)
    have e : (2 * t)⁻¹ * Real.sqrt (2 * t / ((i' + 1 : ℕ) : ℝ)) =
        Real.sqrt (1 / (2 * t)) * (1 / Real.sqrt ((i' + 1 : ℕ) : ℝ)) := by
      rw [Real.sqrt_div (by linarith), one_div, one_div, Real.sqrt_inv]
      have h2t := Real.sqrt_pos.2 (by linarith : (0:ℝ) < 2 * t)
      have e2 := Real.sq_sqrt (by linarith : (0:ℝ) ≤ 2 * t)
      field_simp
      rw [e2]
    rw [e]


theorem telescope {u F : EuclideanSpace ℝ (Fin n) → ℝ} (hu : BM u) (hF : BM F) (N : ℕ) :
    ∫ y, u y * (F y - (Kc t ν)^[N] F y) ∂(chainM ν t) =
      ∑ i ∈ Finset.range N, ∫ y, (Kc t ν)^[i] u y * (F y - Kc t ν F y) ∂(chainM ν t) := by
  haveI := chainM_isProb ν ht
  set a : ℕ → ℝ := fun i => ∫ y, u y * (Kc t ν)^[i] F y ∂(chainM ν t)
  have hterm : ∀ i, ∫ y, (Kc t ν)^[i] u y * (F y - Kc t ν F y) ∂(chainM ν t) = a i - a (i + 1) := by
    intro i
    have hi := iterate_BM ν ht hu i
    simp only [a]
    rw [iterate_selfadj ν ht hu hF i, Function.iterate_succ_apply,
      iterate_selfadj ν ht hu (Kc_BM ν ht hF) i]
    simp_rw [mul_sub]
    rw [integral_sub (hi.mul hF).integrable (hi.mul (Kc_BM ν ht hF)).integrable]
  simp_rw [hterm]
  rw [Finset.sum_range_sub']
  simp only [a, Function.iterate_zero, id]
  simp_rw [mul_sub]
  rw [integral_sub (hu.mul hF).integrable (hu.mul (iterate_BM ν ht hF N)).integrable]

theorem abs_iterate_le {w : EuclideanSpace ℝ (Fin n) → ℝ} (hw : BM w) (N : ℕ) (y : EuclideanSpace ℝ (Fin n)) :
    |(Kc t ν)^[N] w y| ≤ (Kc t ν)^[N] (fun x => |w x|) y := by
  have hwa : BM (fun x => |w x|) := ⟨hw.1.abs, hw.2.choose, fun x => by rw [abs_abs]; exact hw.2.choose_spec x⟩
  rw [abs_le]
  constructor
  · have h1 := iterate_mono ν ht (hwa.const_mul (-1)) hw (fun x => by
      have := neg_abs_le (w x); linarith) N y
    rw [iterate_const_mul ν ht] at h1
    linarith
  · exact iterate_mono ν ht hw hwa (fun x => le_abs_self _) N y

theorem ledoux_main (hν : PhiSobBayes.IsLogConcave ν) {P : ℝ} (hP0 : 0 ≤ P)
    (hP : ∀ g : EuclideanSpace ℝ (Fin n) → ℝ, BM g → Differentiable ℝ g →
      (∃ L, ∀ x, ‖fderiv ℝ g x‖ ≤ L) → variance g ν ≤ P * ∫ x, ‖fderiv ℝ g x‖ ^ 2 ∂ν)
    {u F : EuclideanSpace ℝ (Fin n) → ℝ} (hu : BM u) (hu01 : ∀ y, u y = 0 ∨ u y = 1)
    (hF : BM F) (hFd : Differentiable ℝ F) {LF : ℝ} (hLF : ∀ y, ‖fderiv ℝ F y‖ ≤ LF) (k : ℕ) :
    (1 - (2 * t * P / (1 + 2 * t * P)) ^ k) *
        ((∫ y, u y ∂(chainM ν t)) - (∫ y, u y ∂(chainM ν t)) ^ 2) ≤
      2 * ∫ y, |u y - F y| ∂(chainM ν t) +
        Real.sqrt (1 / (2 * t)) * (Real.pi / 2 + 3 * Real.sqrt (2 * k)) *
          ∫ y, ‖fderiv ℝ F y‖ ∂(chainM ν t) := by
  haveI := chainM_isProb ν ht
  set a := ∫ y, u y ∂(chainM ν t)
  set N := 2 * k
  have hu1 : ∀ y, |u y| ≤ 1 := fun y => by rcases hu01 y with h | h <;> simp [h]
  have hu2 : ∀ y, u y ^ 2 = u y := fun y => by rcases hu01 y with h | h <;> simp [h]
  have hsq : ∫ y, u y ^ 2 ∂(chainM ν t) = a := by simp_rw [hu2]; rfl
  have hup := upper_selfcorr ν ht hP0 hP hu k
  rw [hsq] at hup
  have hw : BM (fun y => u y - F y) := by
    have := hu.add (hF.const_mul (-1)); convert this using 2 with y; ring
  have hNw := iterate_BM ν ht hw N
  have hNF := iterate_BM ν ht hF N
  have hNu := iterate_BM ν ht hu N
  have hNsplit : ∀ y, (Kc t ν)^[N] u y = (Kc t ν)^[N] (fun y => u y - F y) y + (Kc t ν)^[N] F y := by
    intro y
    have := congrFun (iterate_sub ν ht hu hF N) y
    rw [this]; ring
  set A : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun y => u y * ((u y - F y) - (Kc t ν)^[N] (fun y => u y - F y) y)
  set B : EuclideanSpace ℝ (Fin n) → ℝ := fun y => u y * (F y - (Kc t ν)^[N] F y)
  have hAi : Integrable A (chainM ν t) := by
    have := (hu.mul (hw.add (hNw.const_mul (-1)))).integrable (μ := chainM ν t)
    convert this using 2 with y; simp only [A]; ring
  have hBi : Integrable B (chainM ν t) := by
    have := (hu.mul (hF.add (hNF.const_mul (-1)))).integrable (μ := chainM ν t)
    convert this using 2 with y; simp only [B]; ring
  have hkey : a - ∫ y, u y * (Kc t ν)^[N] u y ∂(chainM ν t) =
      ∫ y, A y ∂(chainM ν t) + ∫ y, B y ∂(chainM ν t) := by
    rw [← integral_add hAi hBi]
    have e : ∀ y, A y + B y = u y - u y * (Kc t ν)^[N] u y := by
      intro y
      simp only [A, B]
      rw [hNsplit y]
      have := hu2 y
      nlinarith [this]
    simp_rw [e]
    rw [integral_sub hu.integrable (hu.mul hNu).integrable]
  -- bound A
  have hA : ∫ y, A y ∂(chainM ν t) ≤ 2 * ∫ y, |u y - F y| ∂(chainM ν t) := by
    have hwa : BM (fun x => |u x - F x|) :=
      ⟨hw.1.abs, hw.2.choose, fun x => by rw [abs_abs]; exact hw.2.choose_spec x⟩
    have hpt : ∀ y, A y ≤ |u y - F y| + (Kc t ν)^[N] (fun x => |u x - F x|) y := by
      intro y
      simp only [A]
      have h1 := abs_iterate_le ν ht hw N y
      have h2 := hu1 y
      have h3 : |u y * ((u y - F y) - (Kc t ν)^[N] (fun y => u y - F y) y)| ≤
          |u y - F y| + |(Kc t ν)^[N] (fun y => u y - F y) y| := by
        rw [abs_mul]
        calc |u y| * |u y - F y - (Kc t ν)^[N] (fun y => u y - F y) y|
            ≤ 1 * |u y - F y - (Kc t ν)^[N] (fun y => u y - F y) y| :=
              mul_le_mul_of_nonneg_right h2 (abs_nonneg _)
          _ ≤ _ := by rw [one_mul]; exact abs_sub _ _
      linarith [le_abs_self (u y * ((u y - F y) - (Kc t ν)^[N] (fun y => u y - F y) y))]
    calc ∫ y, A y ∂(chainM ν t) ≤ ∫ y, (|u y - F y| + (Kc t ν)^[N] (fun x => |u x - F x|) y) ∂(chainM ν t) :=
          integral_mono hAi (hwa.integrable.add (iterate_BM ν ht hwa N).integrable) hpt
      _ = 2 * ∫ y, |u y - F y| ∂(chainM ν t) := by
          rw [integral_add hwa.integrable (iterate_BM ν ht hwa N).integrable, int_iterate ν ht hwa N]
          ring
  -- bound B
  have hB : ∫ y, B y ∂(chainM ν t) ≤ Real.sqrt (1 / (2 * t)) * (Real.pi / 2 + 3 * Real.sqrt (2 * k)) *
      ∫ y, ‖fderiv ℝ F y‖ ∂(chainM ν t) := by
    have htel := telescope ν ht hu hF N
    simp only [B]
    rw [htel]
    have hI0 : 0 ≤ ∫ y, ‖fderiv ℝ F y‖ ∂(chainM ν t) := integral_nonneg fun _ => norm_nonneg _
    calc ∑ i ∈ Finset.range N, ∫ y, (Kc t ν)^[i] u y * (F y - Kc t ν F y) ∂(chainM ν t)
        ≤ ∑ i ∈ Finset.range N, Real.sqrt (1 / (2 * t)) *
            (if i = 0 then Real.pi / 2 else 1 / Real.sqrt i) * ∫ y, ‖fderiv ℝ F y‖ ∂(chainM ν t) := by
          apply Finset.sum_le_sum
          intro i _
          exact le_trans (le_abs_self _) (ledoux_term ν ht hν hu hu1 hF hFd hLF i)
      _ = Real.sqrt (1 / (2 * t)) * (∑ i ∈ Finset.range N,
            (if i = 0 then Real.pi / 2 else 1 / Real.sqrt i)) * ∫ y, ‖fderiv ℝ F y‖ ∂(chainM ν t) := by
          rw [Finset.mul_sum, Finset.sum_mul]
      _ ≤ _ := by
          gcongr
          have := sum_inv_sqrt_le N
          simp only [N] at this ⊢
          push_cast at this ⊢
          exact this
  have hq : 0 ≤ (2 * t * P / (1 + 2 * t * P)) ^ k := by positivity
  nlinarith [hup, hkey, hA, hB]

end KB


-- ===== from Solutions/KB/Prior.lean =====

open MeasureTheory ProbabilityTheory
open FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
open scoped RealInnerProductSpace ContDiff

namespace KB
variable {n : ℕ}

/-- Poincaré for differentiable functions from a smooth-test Poincaré inequality. -/
theorem variance_le_of_smoothTest (ρ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ρ]
    (hac : ρ ≪ volume) {C : ℝ} (hC : 0 ≤ C)
    (hS : FunctionalInequalities.Poincare.SmoothTest.Holds ρ C) {F : EuclideanSpace ℝ (Fin n) → ℝ}
    (hF : Differentiable ℝ F) {L : ℝ} (hL : ∀ x, ‖fderiv ℝ F x‖ ≤ L) (hF2 : MemLp F 2 ρ) :
    variance F ρ ≤ C * ∫ x, ‖fderiv ℝ F x‖ ^ 2 ∂ρ := by
  set ρP : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)) := ⟨ρ, inferInstance⟩
  have hS' : FunctionalInequalities.Poincare.SmoothTest.Holds (ρP : Measure (EuclideanSpace ℝ (Fin n)))
      (((C).toNNReal : NNReal) : ℝ) := by
    rw [Real.coe_toNNReal _ hC]; exact hS
  have hLS := (FunctionalInequalities.Poincare.SmoothTest.holds_iff_localSlope_readable ρP volume
    hac _).1 hS'
  have hL0 : 0 ≤ L := le_trans (norm_nonneg _) (hL 0)
  have hlip : LipschitzWith (Real.toNNReal L) F :=
    lipschitzWith_of_nnnorm_fderiv_le hF (fun x => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hL0]; exact hL x)
  have hslope : ∀ x, FunctionalInequalities.Energy.LocalSlope.apply F x =
      ENNReal.ofReal ‖fderiv ℝ F x‖ := by
    intro x
    rw [FunctionalInequalities.Energy.LocalSlope.apply_eq_norm_gradient_readable F x (hF x),
      norm_gradient_eq]
  have hint : Integrable (fun x => ‖fderiv ℝ F x‖ ^ 2) ρ :=
    (integrable_const (L ^ 2)).mono' ((measurable_fderiv ℝ F).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hL x) 2)
  have henergy : FunctionalInequalities.Energy.LocalSlope.energy ρP F =
      ENNReal.ofReal (∫ x, ‖fderiv ℝ F x‖ ^ 2 ∂ρ) := by
    unfold FunctionalInequalities.Energy.LocalSlope.energy
    simp_rw [hslope]
    rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
    congr 1; funext x
    rw [ENNReal.ofReal_pow (norm_nonneg _)]
  have hadm : FunctionalInequalities.Energy.LocalSlope.Admissible ρP F :=
    ⟨hlip.locallyLipschitz, hF2, by rw [henergy]; exact ENNReal.ofReal_ne_top⟩
  have h : evariance F ρ ≤ _ := hLS F hadm
  rw [henergy] at h
  rw [variance, ← ENNReal.toReal_ofReal (mul_nonneg hC (integral_nonneg fun _ => sq_nonneg _))]
  refine ENNReal.toReal_mono ENNReal.ofReal_ne_top ?_
  rw [ENNReal.ofReal_mul hC]
  simpa [Real.coe_toNNReal _ hC, ENNReal.ofReal] using h

theorem smoothTest_of_phi (ρ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure ρ]
    {C : ℝ} (hC : 0 ≤ C) (hP : PhiSobBayes.Poincare ρ C) :
    FunctionalInequalities.Poincare.SmoothTest.Holds ρ C := by
  apply FunctionalInequalities.Poincare.SmoothTest.Holds.of_compactSupport_readable hC
  intro f hf hcs
  have hmem : f ∈ PhiSobBayes.testClass n Set.univ :=
    ⟨⟨0, f, hf.smooth', hcs, by funext x; simp⟩, fun _ => Set.mem_univ _⟩
  exact hP f hmem

/-- the shifted Gaussian `N(x, I/(2t))` as a density measure -/
noncomputable def gaussAt (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) : Measure (EuclideanSpace ℝ (Fin n)) :=
  volume.withDensity (fun y => ENNReal.ofReal (normalizedKernel t (y - x)))

theorem integral_gaussAt {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    ∫ y, f y ∂(gaussAt t x) = heat t f x := by
  unfold gaussAt heat
  have hm : Measurable fun y : EuclideanSpace ℝ (Fin n) => normalizedKernel t (y - x) :=
    (normalizedKernel_measurable t).comp (measurable_id.sub measurable_const)
  rw [integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
    (Filter.Eventually.of_forall fun _ => by simp)]
  congr 1; funext y
  rw [ENNReal.toReal_ofReal (normalizedKernel_pos ht _).le, smul_eq_mul, mul_comm]
  congr 1
  unfold normalizedKernel kernel
  rw [norm_sub_rev]

theorem gaussAt_strongly {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    PhiSobBayes.IsStronglyLogConcave (gaussAt t x) (2 * t) := by
  have hprob : IsProbabilityMeasure (gaussAt t x) := by
    constructor
    unfold gaussAt
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal]
    · have := integral_sub_right_eq_self (μ := (volume : Measure (EuclideanSpace ℝ (Fin n))))
        (fun z => normalizedKernel t z) x
      rw [this, integral_normalizedKernel ht]; simp
    · exact (integrable_normalizedKernel ht).comp_sub_right x
    · exact Filter.Eventually.of_forall fun y => (normalizedKernel_pos ht _).le
  set W : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun y => t * ‖y - x‖ ^ 2 + Real.log (mass (V := EuclideanSpace ℝ (Fin n)) t) with hW
  have hd : ∀ y, HasFDerivAt W ((2 * t) • innerSL ℝ (y - x)) y := by
    intro y
    have := (((hasFDerivAt_id y).sub_const x).norm_sq.const_mul t).add_const
      (Real.log (mass (V := EuclideanSpace ℝ (Fin n)) t))
    refine this.congr_fderiv ?_
    ext v; simp [innerSL_apply_apply]; ring
  have he : fderiv ℝ W = fun y => (2 * t) • innerSL ℝ (y - x) := by
    funext y; exact (hd y).fderiv
  have hd2 : ∀ y, HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => (2 * t) • innerSL ℝ (y - x))
      ((2 * t) • (innerSL ℝ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) y := by
    intro y
    have := ((innerSL ℝ : EuclideanSpace ℝ (Fin n) →L[ℝ] _).hasFDerivAt (x := y - x)).comp y
      ((hasFDerivAt_id y).sub_const x)
    have := this.const_smul (2 * t)
    refine this.congr_fderiv ?_
    ext a b; simp
  refine ⟨hprob, W, fun y => (hd y).differentiableAt, ?_, ?_, ?_⟩
  · rw [he]; exact fun y => (hd2 y).differentiableAt
  · intro y v
    rw [he, (hd2 y).fderiv]
    show 2 * t * ‖v‖ ^ 2 ≤ (2 * t) * ⟪v, v⟫
    rw [real_inner_self_eq_norm_sq]
  · unfold gaussAt
    congr 1; funext y
    congr 1
    show normalizedKernel t (y - x) = Real.exp (-(t * ‖y - x‖ ^ 2 + Real.log (mass (V := EuclideanSpace ℝ (Fin n)) t)))
    rw [neg_add, Real.exp_add, Real.exp_neg (Real.log _), Real.exp_log (mass_pos ht)]
    unfold normalizedKernel kernel
    rw [div_eq_mul_inv, neg_mul]


theorem gaussAt_isProb {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n)) :
    IsProbabilityMeasure (gaussAt t x) := (gaussAt_strongly ht x).1

theorem gauss_var_le {t : ℝ} (ht : 0 < t) (x : EuclideanSpace ℝ (Fin n))
    {g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : BM g) (hgd : Differentiable ℝ g) {L : ℝ}
    (hL : ∀ y, ‖fderiv ℝ g y‖ ≤ L) :
    heat t (fun y => g y ^ 2) x - heat t g x ^ 2 ≤ (1 / (2 * t)) * heat t (fun y => ‖fderiv ℝ g y‖ ^ 2) x := by
  haveI := gaussAt_isProb ht x
  have hP := (PhiSobBayes.fact_A_22 _ (2 * t) (by linarith) (gaussAt_strongly ht x)).1
  have hS := smoothTest_of_phi (gaussAt t x) (by positivity) hP
  have hac : gaussAt t x ≪ volume := withDensity_absolutelyContinuous _ _
  have hm : MemLp g 2 (gaussAt t x) := MemLp.of_bound hg.1.aestronglyMeasurable hg.2.choose
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hg.2.choose_spec y)
  have h := variance_le_of_smoothTest (gaussAt t x) hac (by positivity) hS hgd hL hm
  rw [variance_eq_sub hm] at h
  simp only [Pi.pow_apply] at h
  rw [integral_gaussAt ht, integral_gaussAt ht, integral_gaussAt ht] at h
  exact h

/-- Poincaré inequality for the Gaussian smoothing of a measure satisfying the `L²`-Poincaré
inequality of part A. -/
theorem prior_poincare {μ : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure μ] {C : ℝ}
    (hC : 0 ≤ C)
    (hA : ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, LocallyLipschitz f →
      SongZhangKLS.dirichletEnergy μ f < ⊤ →
        MemLp f 2 μ ∧ evariance f μ ≤ ENNReal.ofReal C * SongZhangKLS.dirichletEnergy μ f)
    {t : ℝ} (ht : 0 < t) :
    ∀ g : EuclideanSpace ℝ (Fin n) → ℝ, BM g → Differentiable ℝ g →
      (∃ L, ∀ x, ‖fderiv ℝ g x‖ ≤ L) →
        variance g (chainM μ t) ≤ (C + 1 / (2 * t)) * ∫ x, ‖fderiv ℝ g x‖ ^ 2 ∂(chainM μ t) := by
  intro g hg hgd ⟨L, hL⟩
  haveI := chainM_isProb μ ht
  have hL0 : 0 ≤ L := le_trans (norm_nonneg _) (hL 0)
  have hg2 := BM.sq hg
  have hG : BM (fun y => ‖fderiv ℝ g y‖ ^ 2) := BM_grad_sq hL
  set h := heat t g
  have hh : BM h := heat_BM ht hg
  have hhd : Differentiable ℝ h := differentiable_heat_of_differentiable ht hg hgd hL
  have hhL : ∀ x, ‖fderiv ℝ h x‖ ≤ L := heat_grad_le ht hg hgd hL
  -- Poincaré for μ applied to h
  have hlip : LipschitzWith (Real.toNNReal L) h :=
    lipschitzWith_of_nnnorm_fderiv_le hhd (fun x => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hL0]; exact hhL x)
  have hintg : Integrable (fun x => ‖fderiv ℝ h x‖ ^ 2) μ :=
    (integrable_const (L ^ 2)).mono' ((measurable_fderiv ℝ h).norm.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (norm_nonneg _) (hhL x) 2)
  have hE : SongZhangKLS.dirichletEnergy μ h = ENNReal.ofReal (∫ x, ‖fderiv ℝ h x‖ ^ 2 ∂μ) := by
    unfold SongZhangKLS.dirichletEnergy
    rw [ofReal_integral_eq_lintegral_ofReal hintg (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
    congr 1; funext x
    rw [← ofReal_norm, norm_gradient_eq, ENNReal.ofReal_pow (norm_nonneg _)]
  have hAh := hA h hlip.locallyLipschitz (by rw [hE]; exact ENNReal.ofReal_lt_top)
  have hvarh : variance h μ ≤ C * ∫ x, ‖fderiv ℝ h x‖ ^ 2 ∂μ := by
    have h2 := hAh.2
    rw [hE, ← ENNReal.ofReal_mul hC] at h2
    rw [variance]
    exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hC (integral_nonneg fun _ => sq_nonneg _)) h2
  have hmh : MemLp h 2 μ := hAh.1
  rw [variance_eq_sub hmh] at hvarh
  simp only [Pi.pow_apply] at hvarh
  -- total variance
  have hmg : MemLp g 2 (chainM μ t) := MemLp.of_bound hg.1.aestronglyMeasurable hg.2.choose
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hg.2.choose_spec y)
  rw [variance_eq_sub hmg]
  simp only [Pi.pow_apply]
  rw [int_chainM μ ht hg2, int_chainM μ ht hg, int_chainM μ ht hG]
  have hloc : ∀ x, heat t (fun y => g y ^ 2) x - h x ^ 2 ≤ (1 / (2 * t)) * heat t (fun y => ‖fderiv ℝ g y‖ ^ 2) x :=
    fun x => gauss_var_le ht x hg hgd hL
  have hcomm : ∀ x, ‖fderiv ℝ h x‖ ^ 2 ≤ heat t (fun y => ‖fderiv ℝ g y‖ ^ 2) x :=
    fun x => norm_fderiv_heat_sq_le_of_differentiable ht hgd hL hg.2.choose_spec x
  have hi1 : ∫ x, (heat t (fun y => g y ^ 2) x - h x ^ 2) ∂μ ≤
      ∫ x, (1 / (2 * t)) * heat t (fun y => ‖fderiv ℝ g y‖ ^ 2) x ∂μ :=
    integral_mono ((heat_BM ht hg2).integrable.sub (BM.sq hh).integrable)
      ((heat_BM ht hG).integrable.const_mul _) hloc
  have hi2 : ∫ x, ‖fderiv ℝ h x‖ ^ 2 ∂μ ≤ ∫ x, heat t (fun y => ‖fderiv ℝ g y‖ ^ 2) x ∂μ :=
    integral_mono hintg (heat_BM ht hG).integrable hcomm
  rw [integral_sub (heat_BM ht hg2).integrable (BM.sq hh).integrable, integral_const_mul] at hi1
  nlinarith [hvarh, hi1, hi2, mul_le_mul_of_nonneg_left hi2 hC]

end KB


-- ===== from Solutions/KB/Assemble.lean =====

open MeasureTheory ProbabilityTheory Filter Topology
open FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
open scoped RealInnerProductSpace ContDiff

namespace KB
variable {n : ℕ}

theorem chainM_eq_smoothedLaw (μ : Measure (EuclideanSpace ℝ (Fin n))) (t : ℝ) :
    chainM μ t = smoothedLaw μ t := rfl

theorem isLogConcave_chainM {μ : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure μ]
    {ρ : EuclideanSpace ℝ (Fin n) → ℝ} (hρ : FunctionalInequalities.KLS.IsBorellDensity μ volume ρ)
    {t : ℝ} (ht : 0 < t) : PhiSobBayes.IsLogConcave (chainM μ t) := by
  have hV2 : ContDiff ℝ 2 (potential ρ t) := potential_contDiff_two hρ ht
  refine ⟨chainM_isProb μ ht, potential ρ t, hV2.differentiable (by norm_num), ?_, ?_, ?_⟩
  · exact (hV2.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  · intro x v
    exact FunctionalInequalities.Analysis.BakryEmery.bilinearIteratedFDerivTwo_nonneg_of_convexOn hV2
      (potential_convex hρ ht) x v
  · rw [chainM_eq_smoothedLaw, smoothedLaw_eq_withDensity_normalizedDensity hρ ht]
    congr 1; funext x
    congr 1
    unfold potential
    rw [neg_neg, Real.exp_log (normalizedDensity_pos hρ ht x)]


section Fcons
variable (A : Set (EuclideanSpace ℝ (Fin n))) (r : ℝ)

/-- Lipschitz cutoff equal to `1` on the `r`-neighbourhood of `A` and `0` beyond `2r`. -/
noncomputable def fr (y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  max 0 (min 1 ((2 * r - Metric.infDist y A) / r))

/-- the shell `{r - h ≤ d(y,A) ≤ 2r + h}` -/
def shell (h : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {y | r - h ≤ Metric.infDist y A ∧ Metric.infDist y A ≤ 2 * r + h}

variable {A r}

theorem fr_mem (y : EuclideanSpace ℝ (Fin n)) : 0 ≤ fr A r y ∧ fr A r y ≤ 1 := by
  unfold fr
  exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem continuous_fr : Continuous (fr A r) := by
  unfold fr
  exact continuous_const.max (continuous_const.min
    ((continuous_const.sub (Metric.continuous_infDist_pt A)).div_const _))

theorem fr_BM : BM (fr A r) :=
  ⟨continuous_fr.measurable, 1, fun y => by
    rw [abs_of_nonneg (fr_mem y).1]; exact (fr_mem y).2⟩

theorem fr_eq_one (hr : 0 < r) {y : EuclideanSpace ℝ (Fin n)} (hy : Metric.infDist y A ≤ r) :
    fr A r y = 1 := by
  unfold fr
  have : 1 ≤ (2 * r - Metric.infDist y A) / r := by rw [le_div_iff₀ hr]; linarith
  rw [min_eq_left this, max_eq_right zero_le_one]

theorem fr_eq_zero (hr : 0 < r) {y : EuclideanSpace ℝ (Fin n)} (hy : 2 * r ≤ Metric.infDist y A) :
    fr A r y = 0 := by
  unfold fr
  have : (2 * r - Metric.infDist y A) / r ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hr.le
  rw [min_eq_right (this.trans zero_le_one), max_eq_left this]

theorem fr_lip (hr : 0 < r) (y z : EuclideanSpace ℝ (Fin n)) :
    |fr A r z - fr A r y| ≤ ‖z - y‖ / r := by
  have hc : LipschitzWith 1 (fun s : ℝ => max 0 (min 1 s)) :=
    (LipschitzWith.id.const_min 1).const_max 0
  have h1 := hc.dist_le_mul ((2 * r - Metric.infDist z A) / r) ((2 * r - Metric.infDist y A) / r)
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at h1
  have h2 : |Metric.infDist z A - Metric.infDist y A| ≤ ‖z - y‖ := by
    have := (Metric.lipschitz_infDist_pt A).dist_le_mul z y
    simpa [Real.dist_eq, dist_eq_norm] using this
  unfold fr
  refine h1.trans ?_
  rw [← sub_div, abs_div, abs_of_pos hr]
  apply div_le_div_of_nonneg_right _ hr.le
  rw [show 2 * r - Metric.infDist z A - (2 * r - Metric.infDist y A) =
    -(Metric.infDist z A - Metric.infDist y A) by ring, abs_neg]
  exact h2

theorem fr_diff_le (hr : 0 < r) (y w : EuclideanSpace ℝ (Fin n)) :
    |fr A r (y + w) - fr A r y| ≤ ‖w‖ / r * (shell A r ‖w‖).indicator (fun _ => (1:ℝ)) y := by
  by_cases hy : y ∈ shell A r ‖w‖
  · rw [Set.indicator_of_mem hy, mul_one]
    have := fr_lip (A := A) hr y (y + w); simpa using this
  · rw [Set.indicator_of_notMem hy, mul_zero, abs_nonpos_iff, sub_eq_zero]
    have hd : |Metric.infDist (y + w) A - Metric.infDist y A| ≤ ‖w‖ := by
      have := (Metric.lipschitz_infDist_pt A).dist_le_mul (y + w) y
      simpa [Real.dist_eq, dist_eq_norm] using this
    simp only [shell, Set.mem_setOf_eq, not_and_or, not_le] at hy
    rcases hy with h | h
    · have hw0 := norm_nonneg w
      rw [fr_eq_one (A := A) (y := y + w) hr (by linarith [(abs_le.1 hd).2]),
        fr_eq_one (A := A) (y := y) hr (by linarith)]
    · have hw0 := norm_nonneg w
      rw [fr_eq_zero (A := A) (y := y + w) hr (by linarith [(abs_le.1 hd).1]),
        fr_eq_zero (A := A) (y := y) hr (by linarith)]

end Fcons


section Fgrad
variable {A : Set (EuclideanSpace ℝ (Fin n))} {r : ℝ}

theorem measurableSet_shell (h : ℝ) : MeasurableSet (shell A r h) := by
  unfold shell
  exact (measurableSet_le measurable_const (Metric.continuous_infDist_pt A).measurable).inter
    (measurableSet_le (Metric.continuous_infDist_pt A).measurable measurable_const)

theorem shell_mono {h h' : ℝ} (hh : h ≤ h') : shell A r h ⊆ shell A r h' := by
  intro y hy
  exact ⟨by linarith [hy.1], by linarith [hy.2]⟩

theorem heat_shift {t : ℝ} (ht : 0 < t) (f : EuclideanSpace ℝ (Fin n) → ℝ) (x c : EuclideanSpace ℝ (Fin n)) :
    heat t f (x + c) = heat t (fun y => f (y + c)) x := by
  rw [heat_eq ht, heat_eq ht]
  congr 1; funext z; rw [add_right_comm]

theorem grad_F_le {t : ℝ} (ht : 0 < t) (hr : 0 < r) (x v : EuclideanSpace ℝ (Fin n)) :
    |fderiv ℝ (heat t (fr A r)) x v| ≤ ‖v‖ / r * ((gaussAt t x) (shell A r 0)).toReal := by
  haveI := gaussAt_isProb ht x
  obtain ⟨hfm, M, hM⟩ := (fr_BM : BM (fr A r))
  have hD := hasFDerivAt_heat' ht hfm hM x
  rw [hD.fderiv]
  set D := heatD t (fr A r) x
  set g : ℝ → ℝ := fun h => heat t (fr A r) (x + h • v)
  have hline : HasDerivAt (fun h : ℝ => x + h • v) v 0 := by
    have := ((hasDerivAt_id (0:ℝ)).smul_const v).const_add x
    simpa using this
  have hg : HasDerivAt g (D v) 0 := by
    have hD' : HasFDerivAt (heat t (fr A r)) D (x + (0:ℝ) • v) := by simpa using hD
    exact hD'.comp_hasDerivAt (0:ℝ) hline
  have hslope := hg.tendsto_slope_zero_right
  set T : ℝ → Set (EuclideanSpace ℝ (Fin n)) := fun h => shell A r (h * (‖v‖ + 1))
  have hT : ∀ h, MeasurableSet (T h) := fun h => measurableSet_shell _
  have hInter : (⋂ h > (0:ℝ), T h) = shell A r 0 := by
    ext y
    simp only [Set.mem_iInter, T, shell, Set.mem_setOf_eq]
    constructor
    · intro H
      have hv1 : 0 < ‖v‖ + 1 := by positivity
      constructor
      · by_contra hc
        push_neg at hc
        have := (H ((r - 0 - Metric.infDist y A) / 2 / (‖v‖ + 1)) (by
          apply div_pos (by linarith) hv1)).1
        rw [div_mul_cancel₀ _ hv1.ne'] at this
        linarith
      · by_contra hc
        push_neg at hc
        have := (H ((Metric.infDist y A - (2 * r + 0)) / 2 / (‖v‖ + 1)) (by
          apply div_pos (by linarith) hv1)).2
        rw [div_mul_cancel₀ _ hv1.ne'] at this
        linarith
    · intro H h hh
      have : 0 ≤ h * (‖v‖ + 1) := by positivity
      exact ⟨by linarith [H.1], by linarith [H.2]⟩
  have hmeas_tend : Tendsto (fun h => ((gaussAt t x) (T h)).toReal) (𝓝[>] 0)
      (𝓝 ((gaussAt t x) (shell A r 0)).toReal) := by
    have := tendsto_measure_biInter_gt (μ := gaussAt t x) (s := T) (a := (0:ℝ))
      (fun h _ => (hT h).nullMeasurableSet)
      (fun i j hi hij => shell_mono (by nlinarith [norm_nonneg v]))
      ⟨1, one_pos, measure_ne_top _ _⟩
    rw [hInter] at this
    exact (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp this
  have hbound : ∀ h > (0:ℝ), |h⁻¹ • (g (0 + h) - g 0)| ≤ ‖v‖ / r * ((gaussAt t x) (T h)).toReal := by
    intro h hh
    simp only [g, zero_add, zero_smul, add_zero, smul_eq_mul]
    rw [heat_shift ht, ← integral_gaussAt ht, ← integral_gaussAt ht]
    have hi1 : Integrable (fun y => fr A r (y + h • v)) (gaussAt t x) :=
      (integrable_const 1).mono' ((continuous_fr).comp (continuous_id.add continuous_const)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, abs_of_nonneg (fr_mem _).1]; exact (fr_mem _).2)
    have hi2 : Integrable (fr A r) (gaussAt t x) := fr_BM.integrable
    rw [← integral_sub hi1 hi2, abs_mul, abs_inv, abs_of_pos hh]
    have hind : ∀ y, |fr A r (y + h • v) - fr A r y| ≤ h * ‖v‖ / r * (T h).indicator (fun _ => (1:ℝ)) y := by
      intro y
      refine (fr_diff_le hr y (h • v)).trans ?_
      rw [norm_smul, Real.norm_of_nonneg hh.le]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Set.indicator_le_indicator_of_subset (shell_mono (by nlinarith [norm_nonneg v]))
        (fun _ => zero_le_one)
    have hint := abs_int_le_int (μ := gaussAt t x)
      (((integrable_const (1:ℝ)).indicator (hT h)).const_mul (h * ‖v‖ / r)) hind
    rw [integral_const_mul] at hint
    have e1 : ∫ a, (T h).indicator (fun _ => (1:ℝ)) a ∂(gaussAt t x) = (gaussAt t x).real (T h) :=
      integral_indicator_one (hT h)
    rw [e1] at hint
    calc h⁻¹ * |∫ y, (fr A r (y + h • v) - fr A r y) ∂(gaussAt t x)|
        ≤ h⁻¹ * (h * ‖v‖ / r * (gaussAt t x).real (T h)) := mul_le_mul_of_nonneg_left hint (by positivity)
      _ = ‖v‖ / r * ((gaussAt t x) (T h)).toReal := by
          rw [Measure.real]; field_simp
  have hlim := hslope.abs
  exact le_of_tendsto_of_tendsto hlim (hmeas_tend.const_mul (‖v‖ / r))
    (eventually_nhdsWithin_of_forall fun h hh => hbound h hh)

end Fgrad


section Fbounds
variable {A : Set (EuclideanSpace ℝ (Fin n))} {r : ℝ}

theorem norm_fderiv_F_le {t : ℝ} (ht : 0 < t) (hr : 0 < r) (x : EuclideanSpace ℝ (Fin n)) :
    ‖fderiv ℝ (heat t (fr A r)) x‖ ≤ 1 / r * ((gaussAt t x) (shell A r 0)).toReal :=
  ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => by
    rw [Real.norm_eq_abs]
    have := grad_F_le (A := A) ht hr x v
    calc _ ≤ ‖v‖ / r * ((gaussAt t x) (shell A r 0)).toReal := this
      _ = _ := by ring

theorem differentiable_F {t : ℝ} (ht : 0 < t) : Differentiable ℝ (heat t (fr A r)) := fun x =>
  (hasFDerivAt_heat' ht fr_BM.1 fr_BM.2.choose_spec x).differentiableAt

theorem integral_norm_sq_gauss {t : ℝ} (ht : 0 < t) :
    ∫ z, ‖z‖ ^ 2 ∂(gaussianLaw (V := EuclideanSpace ℝ (Fin n)) t) = n / (2 * t) := by
  haveI := gaussianLaw_probability (V := EuclideanSpace ℝ (Fin n)) ht
  have e : ∀ z : EuclideanSpace ℝ (Fin n), ‖z‖ ^ 2 =
      ∑ i, ⟪EuclideanSpace.single i (1:ℝ), z⟫ ^ 2 := by
    intro z
    rw [EuclideanSpace.norm_sq_eq]
    congr 1; funext i
    simp [EuclideanSpace.inner_single_left]
  simp_rw [e]
  rw [integral_finset_sum _ (fun i _ => (memLp_inner_gaussian ht _).integrable_sq)]
  simp_rw [FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.gaussianLaw_inner_sq_readable ht]
  simp
  ring

theorem integral_norm_gauss_le {t : ℝ} (ht : 0 < t) :
    ∫ z, ‖z‖ ∂(gaussianLaw (V := EuclideanSpace ℝ (Fin n)) t) ≤ Real.sqrt (n / (2 * t)) := by
  haveI := gaussianLaw_probability (V := EuclideanSpace ℝ (Fin n)) ht
  have hm : MemLp (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖) 2 (gaussianLaw t) := by
    rw [memLp_two_iff_integrable_sq (by fun_prop)]
    have e : (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ 2) =
        fun z => ∑ i, ⟪EuclideanSpace.single i (1:ℝ), z⟫ ^ 2 := by
      funext z
      rw [EuclideanSpace.norm_sq_eq]
      congr 1; funext i
      simp [EuclideanSpace.inner_single_left]
    rw [e]
    exact integrable_finset_sum _ (fun i _ => (memLp_inner_gaussian ht _).integrable_sq)
  have h := sq_integral_le_integral_sq hm
  rw [integral_norm_sq_gauss ht] at h
  exact Real.le_sqrt_of_sq_le h


theorem int_grad_F_le {t : ℝ} (ht : 0 < t) (hr : 0 < r) (m : Measure (EuclideanSpace ℝ (Fin n)))
    [IsProbabilityMeasure m] :
    ∫ x, ‖fderiv ℝ (heat t (fr A r)) x‖ ∂m ≤ 1 / r * (chainM m t).real (shell A r 0) := by
  haveI := chainM_isProb m ht
  have hS := measurableSet_shell (A := A) (r := r) 0
  have hind : BM ((shell A r 0).indicator (fun _ => (1:ℝ))) :=
    ⟨measurable_const.indicator hS, 1, fun y => by
      by_cases hy : y ∈ shell A r 0 <;> simp [Set.indicator, hy]⟩
  have e : ∀ x, ((gaussAt t x) (shell A r 0)).toReal = heat t ((shell A r 0).indicator (fun _ => (1:ℝ))) x := by
    intro x
    haveI := gaussAt_isProb ht x
    rw [← integral_gaussAt ht, integral_indicator_const _ hS, smul_eq_mul, mul_one]; rfl
  have hb : BM (fun x => 1 / r * heat t ((shell A r 0).indicator (fun _ => (1:ℝ))) x) :=
    (heat_BM ht hind).const_mul _
  calc ∫ x, ‖fderiv ℝ (heat t (fr A r)) x‖ ∂m
      ≤ ∫ x, 1 / r * heat t ((shell A r 0).indicator (fun _ => (1:ℝ))) x ∂m := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _) hb.integrable
        exact Filter.Eventually.of_forall fun x => by
          show ‖fderiv ℝ (heat t (fr A r)) x‖ ≤ 1 / r * heat t ((shell A r 0).indicator (fun _ => (1:ℝ))) x
          rw [← e]; exact norm_fderiv_F_le ht hr x
    _ = 1 / r * (chainM m t).real (shell A r 0) := by
        rw [integral_const_mul, ← int_chainM m ht hind, integral_indicator_const _ hS, smul_eq_mul, mul_one]

theorem int_abs_indicator_F_le {t : ℝ} (ht : 0 < t) (hr : 0 < r) (hA : MeasurableSet A)
    (m : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure m] :
    ∫ y, |A.indicator (fun _ => (1:ℝ)) y - heat t (fr A r) y| ∂m ≤
      m.real ({y | Metric.infDist y A < 2 * r} \ A) + 1 / r * Real.sqrt (n / (2 * t)) := by
  haveI := gaussianLaw_probability (V := EuclideanSpace ℝ (Fin n)) ht
  set B := {y | Metric.infDist y A < 2 * r} \ A
  have hB : MeasurableSet B :=
    (measurableSet_lt (Metric.continuous_infDist_pt A).measurable measurable_const).diff hA
  have hpt1 : ∀ y, |A.indicator (fun _ => (1:ℝ)) y - fr A r y| ≤ B.indicator (fun _ => (1:ℝ)) y := by
    intro y
    by_cases hy : y ∈ A
    · rw [Set.indicator_of_mem hy, fr_eq_one hr (by rw [Metric.infDist_zero_of_mem hy]; exact hr.le)]
      simp only [sub_self, abs_zero]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
    · rw [Set.indicator_of_notMem hy, zero_sub, abs_neg, abs_of_nonneg (fr_mem y).1]
      by_cases hd : Metric.infDist y A < 2 * r
      · rw [Set.indicator_of_mem (show y ∈ B from ⟨hd, hy⟩)]; exact (fr_mem y).2
      · rw [fr_eq_zero hr (not_lt.1 hd)]; exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hpt2 : ∀ y, |fr A r y - heat t (fr A r) y| ≤ 1 / r * Real.sqrt (n / (2 * t)) := by
    intro y
    rw [heat_eq ht]
    have : fr A r y - ∫ z, fr A r (y + z) ∂(gaussianLaw t) = ∫ z, (fr A r y - fr A r (y + z)) ∂(gaussianLaw t) := by
      rw [integral_sub (integrable_const _)]; · simp
      exact (integrable_const 1).mono' (continuous_fr.comp (by fun_prop)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs, abs_of_nonneg (fr_mem _).1]; exact (fr_mem _).2)
    rw [this]
    have hint : Integrable (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖) (gaussianLaw t) :=
      (integrable_id_gaussian ht).norm
    calc |∫ z, (fr A r y - fr A r (y + z)) ∂(gaussianLaw t)|
        ≤ ∫ z, 1 / r * ‖z‖ ∂(gaussianLaw t) := by
          refine abs_int_le_int (hint.const_mul _) (fun z => ?_)
          have := fr_lip (A := A) hr y (y + z)
          simpa [div_eq_inv_mul, abs_sub_comm] using this
      _ ≤ 1 / r * Real.sqrt (n / (2 * t)) := by
          rw [integral_const_mul]
          exact mul_le_mul_of_nonneg_left (integral_norm_gauss_le ht) (by positivity)
  have hFb := heat_BM ht (fr_BM (A := A) (r := r))
  have hindA : BM (A.indicator (fun _ => (1:ℝ))) :=
    ⟨measurable_const.indicator hA, 1, fun y => by by_cases hy : y ∈ A <;> simp [Set.indicator, hy]⟩
  have hindB : Integrable (B.indicator (fun _ => (1:ℝ))) m := (integrable_const 1).indicator hB
  calc ∫ y, |A.indicator (fun _ => (1:ℝ)) y - heat t (fr A r) y| ∂m
      ≤ ∫ y, (B.indicator (fun _ => (1:ℝ)) y + 1 / r * Real.sqrt (n / (2 * t))) ∂m := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => abs_nonneg _)
          (hindB.add (integrable_const _))
        refine Filter.Eventually.of_forall fun y => ?_
        calc |A.indicator (fun _ => (1:ℝ)) y - heat t (fr A r) y|
            ≤ |A.indicator (fun _ => (1:ℝ)) y - fr A r y| + |fr A r y - heat t (fr A r) y| := abs_sub_le _ _ _
          _ ≤ _ := add_le_add (hpt1 y) (hpt2 y)
    _ = _ := by
        rw [integral_add hindB (integrable_const _), integral_indicator_const _ hB]
        simp

end Fbounds


theorem q_pow_le_half {t P : ℝ} (ht : 0 < t) (hP : 0 ≤ P) :
    (2 * t * P / (1 + 2 * t * P)) ^ (⌈1 + 2 * t * P⌉₊) ≤ 1 / 2 := by
  set x := 1 / (1 + 2 * t * P)
  have hden : 0 < 1 + 2 * t * P := by positivity
  have hq : 2 * t * P / (1 + 2 * t * P) = 1 - x := by simp only [x]; field_simp; ring
  rw [hq]
  have hx0 : 0 ≤ 1 - x := by
    simp only [x]; rw [sub_nonneg, div_le_one hden]; nlinarith
  have h1 : 1 - x ≤ Real.exp (-x) := by have := Real.add_one_le_exp (-x); linarith
  set k := ⌈1 + 2 * t * P⌉₊
  have hk : 1 + 2 * t * P ≤ k := Nat.le_ceil _
  calc (1 - x) ^ k ≤ Real.exp (-x) ^ k := pow_le_pow_left₀ hx0 h1 k
    _ = Real.exp (-(k * x)) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ Real.exp (-1) := by
        apply Real.exp_le_exp.2
        have : 1 ≤ (k:ℝ) * x := by
          simp only [x]; rw [mul_one_div, le_div_iff₀ hden]; linarith
        linarith
    _ ≤ 1 / 2 := by
        rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
        have := Real.add_one_le_exp (1:ℝ); norm_num at this ⊢; linarith

theorem coef_le {t C : ℝ} (ht : 1 ≤ t) (hC : 0 ≤ C) :
    Real.sqrt (1 / (2 * t)) * (Real.pi / 2 + 3 * Real.sqrt (2 * (⌈1 + 2 * t * (C + 1 / (2 * t))⌉₊ : ℕ))) ≤
      Real.pi / 2 + 3 * Real.sqrt (2 + 2 * (C + 1)) := by
  have ht0 : 0 < t := by linarith
  set k := ⌈1 + 2 * t * (C + 1 / (2 * t))⌉₊
  have hk : (k : ℝ) ≤ 1 + 2 * t * (C + 1 / (2 * t)) + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hs1 : Real.sqrt (1 / (2 * t)) ≤ 1 := by
    rw [Real.sqrt_le_one]; rw [div_le_one (by linarith)]; linarith
  have hs0 : 0 ≤ Real.sqrt (1 / (2 * t)) := Real.sqrt_nonneg _
  have h2 : Real.sqrt (1 / (2 * t)) * Real.sqrt (2 * k) ≤ Real.sqrt (2 + 2 * (C + 1)) := by
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    rw [show 1 / (2 * t) * (2 * (k:ℝ)) = k / t by field_simp, div_le_iff₀ ht0]
    have : 2 * t * (1 / (2 * t)) = 1 := by field_simp
    nlinarith
  nlinarith [Real.pi_pos]

/-- The isoperimetric-type inequality for the smoothed measures. -/
theorem chain_set_ineq {μ : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure μ]
    {ρ : EuclideanSpace ℝ (Fin n) → ℝ} (hρ : FunctionalInequalities.KLS.IsBorellDensity μ volume ρ)
    {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, LocallyLipschitz f →
      SongZhangKLS.dirichletEnergy μ f < ⊤ →
        MemLp f 2 μ ∧ evariance f μ ≤ ENNReal.ofReal C * SongZhangKLS.dirichletEnergy μ f)
    {t : ℝ} (ht1 : 1 ≤ t) {r : ℝ} (hr : 0 < r) {A : Set (EuclideanSpace ℝ (Fin n))}
    (hAm : MeasurableSet A) :
    1 / 2 * ((chainM (chainM μ t) t).real A - (chainM (chainM μ t) t).real A ^ 2) ≤
      2 * ((chainM (chainM μ t) t).real ({y | Metric.infDist y A < 2 * r} \ A) +
        1 / r * Real.sqrt (n / (2 * t))) +
      (Real.pi / 2 + 3 * Real.sqrt (2 + 2 * (C + 1))) * (1 / r *
        (chainM (chainM (chainM μ t) t) t).real (shell A r 0)) := by
  have ht : 0 < t := by linarith
  set ν := chainM μ t
  haveI : IsProbabilityMeasure ν := chainM_isProb μ ht
  set m := chainM ν t
  haveI : IsProbabilityMeasure m := chainM_isProb ν ht
  have hν := isLogConcave_chainM hρ ht
  set P := C + 1 / (2 * t)
  have hP0 : 0 ≤ P := by positivity
  have hP := prior_poincare hC hA ht
  set u := A.indicator (fun _ : EuclideanSpace ℝ (Fin n) => (1:ℝ))
  have hu : BM u := ⟨measurable_const.indicator hAm, 1, fun y => by
    by_cases hy : y ∈ A <;> simp [u, Set.indicator, hy]⟩
  have hu01 : ∀ y, u y = 0 ∨ u y = 1 := fun y => by
    by_cases hy : y ∈ A <;> simp [u, Set.indicator, hy]
  have hF : BM (heat t (fr A r)) := heat_BM ht fr_BM
  have hFd := differentiable_F (A := A) (r := r) ht
  have hLF : ∀ y, ‖fderiv ℝ (heat t (fr A r)) y‖ ≤ 1 / r := by
    intro y
    refine (norm_fderiv_F_le ht hr y).trans ?_
    haveI := gaussAt_isProb ht y
    have : ((gaussAt t y) (shell A r 0)).toReal ≤ 1 := by
      have := prob_le_one (μ := gaussAt t y) (s := shell A r 0)
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
    nlinarith [one_div_pos.2 hr]
  set k := ⌈1 + 2 * t * P⌉₊
  have hL := ledoux_main ν ht hν hP0 hP hu hu01 hF hFd hLF k
  have hint_u : ∫ y, u y ∂m = m.real A := by
    simp only [u]; rw [integral_indicator_const _ hAm, smul_eq_mul, mul_one]
  rw [hint_u] at hL
  have hq := q_pow_le_half ht hP0
  have hcoef := coef_le ht1 hC
  have hgrad := int_grad_F_le (A := A) ht hr m
  have habs := int_abs_indicator_F_le (A := A) ht hr hAm m
  have ha0 : 0 ≤ m.real A - m.real A ^ 2 := by
    have h1 : m.real A ≤ 1 := by
      have := prob_le_one (μ := m) (s := A)
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
    have h0 : 0 ≤ m.real A := measureReal_nonneg
    nlinarith
  have hg0 : 0 ≤ ∫ y, ‖fderiv ℝ (heat t (fr A r)) y‖ ∂m := integral_nonneg fun _ => norm_nonneg _
  have hcoef0 : 0 ≤ Real.sqrt (1 / (2 * t)) * (Real.pi / 2 + 3 * Real.sqrt (2 * (k:ℝ))) := by positivity
  have hK0 : 0 ≤ Real.pi / 2 + 3 * Real.sqrt (2 + 2 * (C + 1)) := by positivity
  calc 1 / 2 * (m.real A - m.real A ^ 2)
      ≤ (1 - (2 * t * P / (1 + 2 * t * P)) ^ k) * (m.real A - m.real A ^ 2) :=
        mul_le_mul_of_nonneg_right (by linarith) ha0
    _ ≤ 2 * ∫ y, |u y - heat t (fr A r) y| ∂m +
          Real.sqrt (1 / (2 * t)) * (Real.pi / 2 + 3 * Real.sqrt (2 * k)) *
            ∫ y, ‖fderiv ℝ (heat t (fr A r)) y‖ ∂m := hL
    _ ≤ _ := by
        have e1 : Real.sqrt (1 / (2 * t)) * (Real.pi / 2 + 3 * Real.sqrt (2 * k)) *
            ∫ y, ‖fderiv ℝ (heat t (fr A r)) y‖ ∂m ≤
            (Real.pi / 2 + 3 * Real.sqrt (2 + 2 * (C + 1))) * (1 / r * (chainM m t).real (shell A r 0)) :=
          mul_le_mul hcoef hgrad hg0 hK0
        linarith

end KB


-- ===== from Solutions/KB/Final.lean =====

open MeasureTheory ProbabilityTheory Filter Topology Complex
open FunctionalInequalities.KLS.LogConcave.GaussianSmoothing
open scoped RealInnerProductSpace ENNReal Pointwise

namespace KB
variable {n : ℕ}

theorem gaussianLaw_conv {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (gaussianLaw (V := EuclideanSpace ℝ (Fin n)) a).conv (gaussianLaw b) =
      gaussianLaw (a * b / (a + b)) := by
  haveI := gaussianLaw_probability (V := EuclideanSpace ℝ (Fin n)) ha
  haveI := gaussianLaw_probability (V := EuclideanSpace ℝ (Fin n)) hb
  have hc : 0 < a * b / (a + b) := by positivity
  haveI := gaussianLaw_probability (V := EuclideanSpace ℝ (Fin n)) hc
  apply Measure.ext_of_charFun
  funext u
  rw [charFun_conv, charFun_gaussianLaw ha, charFun_gaussianLaw hb, charFun_gaussianLaw hc,
    ← Complex.exp_add]
  congr 1
  have ha' : (a:ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb' : (b:ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hab : (a:ℂ) + b ≠ 0 := by exact_mod_cast (by linarith : a + b ≠ 0)
  push_cast
  field_simp
  ring

theorem chainM_chainM {μ : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure μ] {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) : chainM (chainM μ a) b = chainM μ (a * b / (a + b)) := by
  haveI := gaussianLaw_probability (V := EuclideanSpace ℝ (Fin n)) ha
  haveI := gaussianLaw_probability (V := EuclideanSpace ℝ (Fin n)) hb
  unfold chainM
  rw [Measure.conv_assoc, gaussianLaw_conv ha hb]

theorem real_withDensity_eq {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x)
    [hprob : IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (f x)))]
    {B : Set (EuclideanSpace ℝ (Fin n))} (hB : MeasurableSet B) :
    Integrable f ∧ (volume.withDensity (fun x => ENNReal.ofReal (f x))).real B = ∫ x in B, f x := by
  have hlin : ∫⁻ x, ENNReal.ofReal (f x) = 1 := by
    have := hprob.measure_univ
    rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at this
  have hint : Integrable f := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have e : ∀ x, ‖f x‖ₑ = ENNReal.ofReal (f x) := fun x => by
      rw [← ofReal_norm, Real.norm_of_nonneg (hf0 x)]
    simp_rw [e, hlin]; exact ENNReal.one_lt_top
  refine ⟨hint, ?_⟩
  rw [Measure.real, withDensity_apply _ hB, ← ofReal_integral_eq_lintegral_ofReal hint.integrableOn
    (Filter.Eventually.of_forall fun x => hf0 x), ENNReal.toReal_ofReal
    (setIntegral_nonneg hB fun x _ => hf0 x)]

/-- total-variation convergence of Gaussian smoothing for measures with a Borell density -/
theorem tendsto_chainM_real {μ : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure μ]
    {ρ : EuclideanSpace ℝ (Fin n) → ℝ} (hρ : FunctionalInequalities.KLS.IsBorellDensity μ volume ρ)
    {B : Set (EuclideanSpace ℝ (Fin n))} (hB : MeasurableSet B) :
    Tendsto (fun s => (chainM μ s).real B) atTop (𝓝 (μ.real B)) := by
  have hL1 := FunctionalInequalities.KLS.LogConcave.GaussianSmoothing.normalizedDensity_tendsto_L1_readable hρ
  have hμ : μ = volume.withDensity (fun x => ENNReal.ofReal (ρ x)) := hρ.withDensity_eq.symm
  haveI : IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (ρ x))) := by
    rw [← hμ]; infer_instance
  obtain ⟨hρint, hρB⟩ := real_withDensity_eq hρ.measurable hρ.nonneg hB
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) ?_ hL1
  filter_upwards [eventually_gt_atTop (0:ℝ)] with s hs
  have hsm : chainM μ s = volume.withDensity (fun x => ENNReal.ofReal (normalizedDensity ρ s x)) := by
    rw [chainM_eq_smoothedLaw, smoothedLaw_eq_withDensity_normalizedDensity hρ hs]
  haveI : IsProbabilityMeasure (volume.withDensity (fun x => ENNReal.ofReal (normalizedDensity ρ s x))) := by
    rw [← hsm]; exact chainM_isProb μ (by linarith)
  obtain ⟨hnint, hnB⟩ := real_withDensity_eq (normalizedDensity_measurable hρ.measurable hs)
    (fun x => (normalizedDensity_pos hρ hs x).le) hB
  rw [hsm, hnB, hμ, hρB, Real.norm_eq_abs, ← integral_sub hnint.integrableOn hρint.integrableOn]
  calc |∫ x in B, (normalizedDensity ρ s x - ρ x)| ≤ ∫ x in B, |normalizedDensity ρ s x - ρ x| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ x, |normalizedDensity ρ s x - ρ x| :=
        setIntegral_le_integral (hnint.sub hρint).abs (Filter.Eventually.of_forall fun _ => abs_nonneg _)


theorem limit_ineq {μ : Measure (EuclideanSpace ℝ (Fin n))} [IsProbabilityMeasure μ]
    {ρ : EuclideanSpace ℝ (Fin n) → ℝ} (hρ : FunctionalInequalities.KLS.IsBorellDensity μ volume ρ)
    {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, LocallyLipschitz f →
      SongZhangKLS.dirichletEnergy μ f < ⊤ →
        MemLp f 2 μ ∧ evariance f μ ≤ ENNReal.ofReal C * SongZhangKLS.dirichletEnergy μ f)
    {r : ℝ} (hr : 0 < r) {A : Set (EuclideanSpace ℝ (Fin n))} (hAm : MeasurableSet A) :
    1 / 2 * (μ.real A - μ.real A ^ 2) ≤
      2 * μ.real ({y | Metric.infDist y A < 2 * r} \ A) +
      (Real.pi / 2 + 3 * Real.sqrt (2 + 2 * (C + 1))) * (1 / r * μ.real (shell A r 0)) := by
  set B := {y | Metric.infDist y A < 2 * r} \ A
  have hBm : MeasurableSet B :=
    (measurableSet_lt (Metric.continuous_infDist_pt A).measurable measurable_const).diff hAm
  have hSm : MeasurableSet (shell A r 0) := measurableSet_shell 0
  have h2 : ∀ t : ℝ, 0 < t → chainM (chainM μ t) t = chainM μ (t / 2) := by
    intro t ht
    rw [chainM_chainM ht ht]; congr 1; field_simp; ring
  have h3 : ∀ t : ℝ, 0 < t → chainM (chainM (chainM μ t) t) t = chainM μ (t / 3) := by
    intro t ht
    rw [h2 t ht]
    haveI := chainM_isProb μ (by linarith : (0:ℝ) < t / 2)
    rw [chainM_chainM (by linarith) ht]; congr 1; field_simp; ring
  have hlim2 : ∀ X, MeasurableSet X → Tendsto (fun t : ℝ => (chainM μ (t / 2)).real X) atTop (𝓝 (μ.real X)) :=
    fun X hX => (tendsto_chainM_real hρ hX).comp (tendsto_id.atTop_div_const (by norm_num))
  have hlim3 : ∀ X, MeasurableSet X → Tendsto (fun t : ℝ => (chainM μ (t / 3)).real X) atTop (𝓝 (μ.real X)) :=
    fun X hX => (tendsto_chainM_real hρ hX).comp (tendsto_id.atTop_div_const (by norm_num))
  have hsq : Tendsto (fun t : ℝ => Real.sqrt (n / (2 * t))) atTop (𝓝 0) := by
    have : Tendsto (fun t : ℝ => (n:ℝ) / (2 * t)) atTop (𝓝 0) := by
      have := (tendsto_const_nhds (x := (n:ℝ))).div_atTop
        (tendsto_id.const_mul_atTop (by norm_num : (0:ℝ) < 2))
      simpa using this
    have := (Real.continuous_sqrt.tendsto 0).comp this
    rw [Real.sqrt_zero] at this
    exact this
  have hL : Tendsto (fun t : ℝ => 1 / 2 * ((chainM μ (t / 2)).real A - (chainM μ (t / 2)).real A ^ 2))
      atTop (𝓝 (1 / 2 * (μ.real A - μ.real A ^ 2))) :=
    ((hlim2 A hAm).sub ((hlim2 A hAm).pow 2)).const_mul _
  have hR : Tendsto (fun t : ℝ => 2 * ((chainM μ (t / 2)).real B + 1 / r * Real.sqrt (n / (2 * t))) +
      (Real.pi / 2 + 3 * Real.sqrt (2 + 2 * (C + 1))) * (1 / r * (chainM μ (t / 3)).real (shell A r 0)))
      atTop (𝓝 (2 * (μ.real B + 1 / r * 0) +
        (Real.pi / 2 + 3 * Real.sqrt (2 + 2 * (C + 1))) * (1 / r * μ.real (shell A r 0)))) :=
    (((hlim2 B hBm).add (hsq.const_mul _)).const_mul _).add (((hlim3 _ hSm).const_mul _).const_mul _)
  have key := le_of_tendsto_of_tendsto hL hR (by
    filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht1
    have ht : 0 < t := by linarith
    have := chain_set_ineq hρ hC hA ht1 hr hAm
    rw [h3 t ht, h2 t ht] at this
    exact this)
  simpa using key


theorem mem_add_ball_of_infDist_lt {A : Set (EuclideanSpace ℝ (Fin n))} (hne : A.Nonempty)
    {ε : ℝ} (hε : 0 < ε) {y : EuclideanSpace ℝ (Fin n)} (hy : Metric.infDist y A < ε) :
    y ∈ A + ε • Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := by
  obtain ⟨a, ha, hya⟩ := (Metric.infDist_lt_iff hne).1 hy
  refine ⟨a, ha, y - a, ?_, by abel⟩
  refine ⟨ε⁻¹ • (y - a), ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hε.le)]
    rw [dist_eq_norm] at hya
    rw [inv_mul_le_iff₀ hε]; linarith
  · simp [smul_smul, hε.ne']

theorem cheeger_bound {μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))}
    (hlc : FunctionalInequalities.KLS.LogConcave μ) (hiso : FunctionalInequalities.KLS.Isotropic μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hA : ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, LocallyLipschitz f →
      SongZhangKLS.dirichletEnergy (μ : Measure (EuclideanSpace ℝ (Fin n))) f < ⊤ →
        MemLp f 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
        evariance f (μ : Measure (EuclideanSpace ℝ (Fin n))) ≤
          ENNReal.ofReal C * SongZhangKLS.dirichletEnergy (μ : Measure (EuclideanSpace ℝ (Fin n))) f) :
    SongZhangKLS.cheegerPsi (μ : Measure (EuclideanSpace ℝ (Fin n))) ≤
      ENNReal.ofReal (2 * (4 + 6 * (Real.pi / 2 + 3 * Real.sqrt (2 + 2 * (C + 1))))) := by
  set K := Real.pi / 2 + 3 * Real.sqrt (2 + 2 * (C + 1))
  have hK : 0 < K := by positivity
  obtain ⟨ρ, hρ⟩ := FunctionalInequalities.KLS.LogConcave.exists_isBorellDensity_of_interior_support_nonempty
    hlc volume (SZPartA.interior_support_nonempty hlc hiso) (SZPartA.absolutelyContinuous volume hlc hiso)
  set ν : Measure (EuclideanSpace ℝ (Fin n)) := (μ : Measure (EuclideanSpace ℝ (Fin n)))
  unfold SongZhangKLS.cheegerPsi
  refine iSup₂_le fun A ⟨hAm, hpos, hlt1⟩ => ?_
  have hne : A.Nonempty := MeasureTheory.nonempty_of_measure_ne_zero hpos.ne'
  set a := ν.real A
  have hAeq : ν A = ENNReal.ofReal a := (ofReal_measureReal (measure_ne_top _ _)).symm
  have ha0 : 0 < a := by
    rw [hAeq] at hpos; exact ENNReal.ofReal_pos.1 hpos
  have ha1 : a < 1 := by
    rw [hAeq] at hlt1; exact (ENNReal.ofReal_lt_one).1 hlt1
  set c0 := a * (1 - a) / (4 + 6 * K)
  have hc0 : 0 < c0 := by
    apply div_pos (mul_pos ha0 (by linarith)) (by positivity)
  -- lower bound on the outer boundary measure
  have hbd : ENNReal.ofReal c0 ≤ SongZhangKLS.outerBoundary ν A := by
    unfold SongZhangKLS.outerBoundary
    apply le_liminf_of_le (by isBoundedDefault)
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with ε hε
    obtain ⟨hε0, hε1⟩ := hε
    set Aε := A + ε • Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1
    have hsub : A ⊆ Aε := by
      intro y hy
      exact ⟨y, hy, 0, ⟨0, Metric.mem_closedBall_self zero_le_one, by simp⟩, by simp⟩
    set r := ε / 3
    have hr : 0 < r := by positivity
    have hlim := limit_ineq hρ hC hA hr hAm
    set B := {y | Metric.infDist y A < 2 * r} \ A
    have hBm : MeasurableSet B :=
      (measurableSet_lt (Metric.continuous_infDist_pt A).measurable measurable_const).diff hAm
    have hSm : MeasurableSet (shell A r 0) := measurableSet_shell 0
    have hBsub : A ∪ B ⊆ Aε := by
      rintro y (hy | hy)
      · exact hsub hy
      · have hr3 : r = ε / 3 := rfl
        exact mem_add_ball_of_infDist_lt hne hε0 (by have := hy.1; simp only [Set.mem_setOf_eq] at this; linarith)
    have hSsub : A ∪ shell A r 0 ⊆ Aε := by
      rintro y (hy | hy)
      · exact hsub hy
      · have hr3 : r = ε / 3 := rfl
        exact mem_add_ball_of_infDist_lt hne hε0 (by have := hy.2; linarith)
    have hBdisj : Disjoint A B := Set.disjoint_sdiff_right
    have hSdisj : Disjoint A (shell A r 0) := by
      rw [Set.disjoint_left]
      intro y hyA hyS
      have := hyS.1
      rw [Metric.infDist_zero_of_mem hyA] at this
      linarith
    set D := ν Aε - ν A
    have hDB : ν B ≤ D := by
      have := measure_mono (μ := ν) hBsub
      rw [measure_union hBdisj hBm] at this
      exact ENNReal.le_sub_of_add_le_left (measure_ne_top _ _) this
    have hDS : ν (shell A r 0) ≤ D := by
      have := measure_mono (μ := ν) hSsub
      rw [measure_union hSdisj hSm] at this
      exact ENNReal.le_sub_of_add_le_left (measure_ne_top _ _) this
    have hDfin : D ≠ ⊤ := ne_top_of_le_ne_top (measure_ne_top ν Aε) tsub_le_self
    have hBr : ν.real B ≤ D.toReal := ENNReal.toReal_mono hDfin hDB
    have hSr : ν.real (shell A r 0) ≤ D.toReal := ENNReal.toReal_mono hDfin hDS
    have hD0 : 0 ≤ D.toReal := ENNReal.toReal_nonneg
    -- real inequality
    have hreal : c0 * ε ≤ D.toReal := by
      have h1 : 1 / 2 * (a - a ^ 2) ≤ 2 * D.toReal + K * (1 / r * D.toReal) := by
        refine hlim.trans ?_
        gcongr
      have h2 : 1 / 2 * (a - a ^ 2) ≤ (2 + 3 * K / ε) * D.toReal := by
        have : K * (1 / r * D.toReal) = 3 * K / ε * D.toReal := by simp only [r]; field_simp
        linarith
      simp only [c0]
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have h3 : a * (1 - a) * ε ≤ (4 * ε + 6 * K) * D.toReal := by
        have := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ 2 * ε)
        have e : 2 * ε * ((2 + 3 * K / ε) * D.toReal) = (4 * ε + 6 * K) * D.toReal := by
          field_simp; ring
        nlinarith
      nlinarith
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp [hε0])) (Or.inl ENNReal.ofReal_ne_top),
      ← ENNReal.ofReal_mul hc0.le, ← ENNReal.ofReal_toReal hDfin]
    exact ENNReal.ofReal_le_ofReal hreal
  -- conclude
  have hmin : min (ν A) (1 - ν A) ≤ ENNReal.ofReal (2 * a * (1 - a)) := by
    rw [hAeq]
    rcases le_total a (1 / 2) with h | h
    · refine (min_le_left _ _).trans (ENNReal.ofReal_le_ofReal ?_); nlinarith
    · refine (min_le_right _ _).trans ?_
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ ha0.le]
      exact ENNReal.ofReal_le_ofReal (by nlinarith)
  have hob0 : SongZhangKLS.outerBoundary ν A ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hc0) hbd)
  rw [ENNReal.div_le_iff_le_mul (Or.inl hob0)
    (Or.inr (ne_of_gt (ENNReal.ofReal_pos.2 (by positivity))))]
  refine hmin.trans ?_
  calc ENNReal.ofReal (2 * a * (1 - a)) = ENNReal.ofReal (2 * (4 + 6 * K)) * ENNReal.ofReal c0 := by
        rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; simp only [c0]; field_simp
    _ ≤ ENNReal.ofReal (2 * (4 + 6 * K)) * SongZhangKLS.outerBoundary ν A := by gcongr

end KB

theorem KB_cheeger_universal :
    ∃ C' : ℝ, 0 < C' ∧ ∀ (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))),
      FunctionalInequalities.KLS.LogConcave μ → FunctionalInequalities.KLS.Isotropic μ →
      SongZhangKLS.cheegerPsi (μ : Measure (EuclideanSpace ℝ (Fin n))) ≤ ENNReal.ofReal C' := by
  obtain ⟨C, hC, hA⟩ := SZPartA.partA
  refine ⟨2 * (4 + 6 * (Real.pi / 2 + 3 * Real.sqrt (2 + 2 * (C + 1)))), by positivity, ?_⟩
  intro n μ hlc hiso
  exact KB.cheeger_bound hlc hiso hC.le (hA n μ hlc hiso)


theorem solution :
    ∃ C' : ℝ, 0 < C' ∧ ∀ (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))),
      FunctionalInequalities.KLS.LogConcave μ → FunctionalInequalities.KLS.Isotropic μ →
      SongZhangKLS.cheegerPsi (μ : MeasureTheory.Measure (EuclideanSpace ℝ (Fin n))) ≤ ENNReal.ofReal C' :=
  KB_cheeger_universal
