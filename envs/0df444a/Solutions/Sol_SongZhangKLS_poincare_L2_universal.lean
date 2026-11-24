-- Prove2me | solution 1 for SongZhangKLS.poincare_L2_universal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-24T08:35:55.40798+00:00
-- url     : https://prove2.me/submissions/841c6a62-7233-45cf-b353-6753ae70fc15

import Mathlib
import Definitions.Def_SongZhangKLS_poincareConst
import Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_exists_isotropicBound_readable
import Theorems.Thm_FunctionalInequalities_KLS_LogConcave_exists_smoothGradient_localDensity_readable
import Theorems.Thm_FunctionalInequalities_Energy_LocalSlope_apply_eq_norm_gradient_readable

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

theorem solution :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (μ : ProbabilityMeasure (EuclideanSpace ℝ (Fin n))),
      FunctionalInequalities.KLS.LogConcave μ → FunctionalInequalities.KLS.Isotropic μ →
      ∀ f : EuclideanSpace ℝ (Fin n) → ℝ, LocallyLipschitz f →
        SongZhangKLS.dirichletEnergy (μ : Measure (EuclideanSpace ℝ (Fin n))) f < ⊤ →
        MemLp f 2 (μ : Measure (EuclideanSpace ℝ (Fin n))) ∧
        evariance f (μ : Measure (EuclideanSpace ℝ (Fin n))) ≤
          ENNReal.ofReal C * SongZhangKLS.dirichletEnergy (μ : Measure (EuclideanSpace ℝ (Fin n))) f :=
  SZPartA.partA
