-- Prove2me | solution 1 for Penrose.delta_laplacian
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T08:53:55.536992+00:00
-- url     : https://prove2.me/submissions/d1cd500d-4005-44cd-a84b-7c7d8d03493f

import Mathlib
import Definitions.Def_penrose
import Definitions.Def_penrose_energy


open MeasureTheory Metric Real
open scoped Pointwise ENNReal RealInnerProductSpace

namespace PenAux

abbrev Space := EuclideanSpace ℝ (Fin 3)




/-- coordinates `x ↦ (x 0, (x 1, x 2))` preserve volume -/
lemma coord_mp : MeasurePreserving (fun x : Space => (x.ofLp 0, (x.ofLp 1, x.ofLp 2)))
    volume volume := by
  have h1 := PiLp.volume_preserving_ofLp (Fin 3)
  have h2 := measurePreserving_piFinSuccAbove (fun _ : Fin 3 => (volume : Measure ℝ)) 0
  have h3 := (MeasurePreserving.id (volume : Measure ℝ)).prod (volume_preserving_finTwoArrow ℝ)
  have h4 := h3.comp (h2.comp h1)
  have heq : (fun x : Space => (x.ofLp 0, (x.ofLp 1, x.ofLp 2))) =
      Prod.map id ⇑MeasurableEquiv.finTwoArrow ∘
        ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 0) ∘ WithLp.ofLp := by
    funext x; rfl
  rw [heq]; exact h4

lemma norm_sq_coord (x : Space) : ‖x‖ ^ 2 = x.ofLp 0 ^ 2 + x.ofLp 1 ^ 2 + x.ofLp 2 ^ 2 := by
  rw [EuclideanSpace.norm_eq, sq_sqrt (by positivity), Fin.sum_univ_three]
  simp [sq_abs]

lemma polar_radial (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    ∫⁻ q : ℝ × ℝ, g (q.1 ^ 2 + q.2 ^ 2) =
      ENNReal.ofReal (2 * π) * ∫⁻ r in Set.Ioi 0, ENNReal.ofReal r * g (r ^ 2) := by
  rw [← lintegral_comp_polarCoord_symm, polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have : ∀ p : ℝ × ℝ, ENNReal.ofReal p.1 • g ((polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2)
      = (ENNReal.ofReal p.1 * g (p.1 ^ 2)) * (fun _ : ℝ => (1 : ℝ≥0∞)) p.2 := by
    intro p
    simp only [polarCoord_symm_apply, smul_eq_mul, mul_one]
    congr 2
    nlinarith [cos_sq_add_sin_sq p.2]
  simp_rw [this]
  have h := lintegral_prod_mul (μ := volume.restrict (Set.Ioi 0))
    (ν := volume.restrict (Set.Ioo (-π) π)) (f := fun r => ENNReal.ofReal r * g (r ^ 2))
    (g := fun _ => (1 : ℝ≥0∞)) (by fun_prop) (by fun_prop)
  try simp only at h
  rw [h]
  simp only [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    volume_Ioo, one_mul]
  rw [mul_comm]; congr 2; ring

lemma lint_sq_Ioo : ∫⁻ s in Set.Ioo (0:ℝ) 1, ENNReal.ofReal (s ^ 2) = ENNReal.ofReal (1 / 3) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · rw [integral_Ioc_eq_integral_Ioo.symm, ← intervalIntegral.integral_of_le zero_le_one,
      integral_pow]
    norm_num
  · exact (continuous_pow 2).integrableOn_Icc.mono_set Set.Ioo_subset_Icc_self
  · exact Filter.Eventually.of_forall fun s => sq_nonneg s

lemma lint_cos_change (F : ℝ → ℝ≥0∞) :
    ∫⁻ θ in Set.Ioo 0 π, ENNReal.ofReal (sin θ) * F (cos θ) =
      ∫⁻ t in Set.Ioo (-1) 1, F t := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (s := Set.Icc 0 π) (f := cos)
    (f' := fun x => -sin x) measurableSet_Icc
    (fun x _ => (hasDerivAt_cos x).hasDerivWithinAt) injOn_cos F
  rw [bijOn_cos.image_eq] at h
  rw [Measure.restrict_congr_set Ioo_ae_eq_Icc, Measure.restrict_congr_set Ioo_ae_eq_Icc, h]
  refine setLIntegral_congr_fun measurableSet_Icc (fun x hx => ?_)
  rw [abs_neg, abs_of_nonneg (sin_nonneg_of_nonneg_of_le_pi hx.1 hx.2)]

lemma lint_theta (F : ℝ → ℝ≥0∞) :
    ∫⁻ θ in Set.Ioo (-π) π, (Set.Ioi (0:ℝ)).indicator (fun t => ENNReal.ofReal t) (sin θ) * F (cos θ)
      = ∫⁻ t in Set.Ioo (-1) 1, F t := by
  rw [← lint_cos_change]
  have : ∀ θ ∈ Set.Ioo (-π) π,
      (Set.Ioi (0:ℝ)).indicator (fun t => ENNReal.ofReal t) (sin θ) * F (cos θ) =
      (Set.Ioo 0 π).indicator (fun θ => ENNReal.ofReal (sin θ) * F (cos θ)) θ := by
    intro θ hθ
    by_cases h0 : 0 < θ
    · have hs : 0 < sin θ := sin_pos_of_pos_of_lt_pi h0 hθ.2
      rw [Set.indicator_of_mem (show sin θ ∈ Set.Ioi 0 from hs),
        Set.indicator_of_mem (show θ ∈ Set.Ioo 0 π from ⟨h0, hθ.2⟩)]
    · push Not at h0
      have hs : sin θ ≤ 0 := sin_nonpos_of_nonpos_of_neg_pi_le h0 hθ.1.le
      rw [Set.indicator_of_notMem (show sin θ ∉ Set.Ioi 0 from fun h => absurd h (not_lt.2 hs)),
        Set.indicator_of_notMem (show θ ∉ Set.Ioo 0 π from fun h => absurd h.1 (not_lt.2 h0))]
      simp
  rw [setLIntegral_congr_fun measurableSet_Ioo this, lintegral_indicator measurableSet_Ioo,
    Measure.restrict_restrict measurableSet_Ioo]
  congr 2
  ext θ; constructor
  · rintro ⟨h1, -⟩; exact h1
  · intro h; exact ⟨h, by linarith [h.1, pi_pos], h.2⟩

lemma polar_half (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ q : ℝ × ℝ, (Set.Ioi (0:ℝ)).indicator (fun r => ENNReal.ofReal r) q.2 *
        ((Set.Iio (1:ℝ)).indicator 1 (q.1 ^ 2 + q.2 ^ 2) * F (q.1 / √(q.1 ^ 2 + q.2 ^ 2))) =
      ENNReal.ofReal (1 / 3) * ∫⁻ t in Set.Ioo (-1) 1, F t := by
  rw [← lintegral_comp_polarCoord_symm, polarCoord_target]
  have key : ∀ p ∈ Set.Ioi (0:ℝ) ×ˢ Set.Ioo (-π) π,
      ENNReal.ofReal p.1 • ((Set.Ioi (0:ℝ)).indicator (fun r => ENNReal.ofReal r) (polarCoord.symm p).2 *
        ((Set.Iio (1:ℝ)).indicator 1 ((polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2) *
          F ((polarCoord.symm p).1 / √((polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2)))) =
      (Set.Iio (1:ℝ)).indicator (fun s => ENNReal.ofReal (s ^ 2)) p.1 *
        ((Set.Ioi (0:ℝ)).indicator (fun t => ENNReal.ofReal t) (sin p.2) * F (cos p.2)) := by
    rintro ⟨s, θ⟩ ⟨hs, hθ⟩
    simp only [Set.mem_Ioi] at hs
    simp only [polarCoord_symm_apply, smul_eq_mul]
    have h1 : (s * cos θ) ^ 2 + (s * sin θ) ^ 2 = s ^ 2 := by
      nlinarith [cos_sq_add_sin_sq θ]
    rw [h1, sqrt_sq hs.le, mul_div_cancel_left₀ _ hs.ne']
    have hsin : (Set.Ioi (0:ℝ)).indicator (fun r => ENNReal.ofReal r) (s * sin θ) =
        ENNReal.ofReal s * (Set.Ioi (0:ℝ)).indicator (fun t => ENNReal.ofReal t) (sin θ) := by
      by_cases h : 0 < sin θ
      · rw [Set.indicator_of_mem (show s * sin θ ∈ Set.Ioi 0 from mul_pos hs h),
          Set.indicator_of_mem (show sin θ ∈ Set.Ioi 0 from h), ENNReal.ofReal_mul hs.le]
      · rw [Set.indicator_of_notMem (show s * sin θ ∉ Set.Ioi 0 from fun h' => h (pos_of_mul_pos_right h' hs.le)),
          Set.indicator_of_notMem (show sin θ ∉ Set.Ioi 0 from h)]
        simp
    rw [hsin]
    by_cases h2 : s < 1
    · have h2' : s ^ 2 < 1 := by nlinarith
      rw [Set.indicator_of_mem (show s ^ 2 ∈ Set.Iio 1 from h2'),
        Set.indicator_of_mem (show s ∈ Set.Iio 1 from h2), ENNReal.ofReal_pow hs.le]
      simp only [Pi.one_apply, mul_one]
      ring
    · have h2' : ¬ s ^ 2 < 1 := by nlinarith
      rw [Set.indicator_of_notMem (show s ^ 2 ∉ Set.Iio 1 from h2'),
        Set.indicator_of_notMem (show s ∉ Set.Iio 1 from h2)]
      simp
  rw [setLIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) key,
    Measure.volume_eq_prod, ← Measure.prod_restrict]
  have h := lintegral_prod_mul (μ := volume.restrict (Set.Ioi 0))
    (ν := volume.restrict (Set.Ioo (-π) π))
    (f := (Set.Iio (1:ℝ)).indicator (fun s => ENNReal.ofReal (s ^ 2)))
    (g := fun θ => (Set.Ioi (0:ℝ)).indicator (fun t => ENNReal.ofReal t) (sin θ) * F (cos θ))
    ((Measurable.indicator (by fun_prop) measurableSet_Iio).aemeasurable)
    ((((Measurable.indicator ENNReal.measurable_ofReal measurableSet_Ioi).comp measurable_sin).mul
      (hF.comp measurable_cos)).aemeasurable)
  rw [h, lint_theta, lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio]
  rw [show Set.Iio (1:ℝ) ∩ Set.Ioi 0 = Set.Ioo 0 1 by ext; simp [and_comm], lint_sq_Ioo]

lemma cone_lintegral (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x : Space, (Set.Iio (1:ℝ)).indicator 1 (‖x‖ ^ 2) * F (x.ofLp 0 / ‖x‖) =
      ENNReal.ofReal (2 * π) * (ENNReal.ofReal (1 / 3) * ∫⁻ t in Set.Ioo (-1) 1, F t) := by
  set Q : ℝ × (ℝ × ℝ) → ℝ≥0∞ := fun p => (Set.Iio (1:ℝ)).indicator 1 (p.1 ^ 2 + (p.2.1 ^ 2 + p.2.2 ^ 2)) *
    F (p.1 / √(p.1 ^ 2 + (p.2.1 ^ 2 + p.2.2 ^ 2))) with hQ
  have hQm : Measurable Q := by
    apply Measurable.mul
    · exact (measurable_one.indicator measurableSet_Iio).comp (by fun_prop)
    · exact hF.comp (by fun_prop)
  have h1 : ∀ x : Space, (Set.Iio (1:ℝ)).indicator 1 (‖x‖ ^ 2) * F (x.ofLp 0 / ‖x‖) =
      Q (x.ofLp 0, (x.ofLp 1, x.ofLp 2)) := by
    intro x
    have hn : ‖x‖ ^ 2 = x.ofLp 0 ^ 2 + (x.ofLp 1 ^ 2 + x.ofLp 2 ^ 2) := by
      rw [norm_sq_coord]; ring
    simp only [hQ]
    rw [← hn, sqrt_sq (norm_nonneg x)]
  simp_rw [h1]
  rw [coord_mp.lintegral_comp hQm, Measure.volume_eq_prod, lintegral_prod _ hQm.aemeasurable]
  have h2 : ∀ z : ℝ, ∫⁻ q : ℝ × ℝ, Q (z, q) = ENNReal.ofReal (2 * π) *
      ∫⁻ r, (Set.Ioi (0:ℝ)).indicator (fun r => ENNReal.ofReal r) r *
        ((Set.Iio (1:ℝ)).indicator 1 (z ^ 2 + r ^ 2) * F (z / √(z ^ 2 + r ^ 2))) := by
    intro z
    have := polar_radial (fun w => (Set.Iio (1:ℝ)).indicator 1 (z ^ 2 + w) * F (z / √(z ^ 2 + w)))
      (by
        apply Measurable.mul
        · exact (measurable_one.indicator measurableSet_Iio).comp (by fun_prop)
        · exact hF.comp (by fun_prop))
    try simp only at this
    rw [this, ← lintegral_indicator measurableSet_Ioi]
    congr 2; funext r
    by_cases hr : r ∈ Set.Ioi (0:ℝ)
    · simp [Set.indicator_of_mem hr]
    · simp [Set.indicator_of_notMem hr]
  simp_rw [h2]
  have hHm : Measurable (fun q : ℝ × ℝ => (Set.Ioi (0:ℝ)).indicator (fun r => ENNReal.ofReal r) q.2 *
        ((Set.Iio (1:ℝ)).indicator 1 (q.1 ^ 2 + q.2 ^ 2) * F (q.1 / √(q.1 ^ 2 + q.2 ^ 2)))) := by
    refine Measurable.mul ?_ (Measurable.mul ?_ ?_)
    · exact (ENNReal.measurable_ofReal.indicator measurableSet_Ioi).comp measurable_snd
    · exact (measurable_one.indicator measurableSet_Iio).comp (by fun_prop)
    · exact hF.comp (by fun_prop)
  rw [lintegral_const_mul _ (Measurable.lintegral_prod_right' (ν := volume) hHm)]
  congr 1
  rw [← polar_half F hF, Measure.volume_eq_prod, lintegral_prod]
  refine Measurable.aemeasurable (Measurable.mul ?_ (Measurable.mul ?_ ?_))
  · exact (ENNReal.measurable_ofReal.indicator measurableSet_Ioi).comp measurable_snd
  · exact (measurable_one.indicator measurableSet_Iio).comp (by fun_prop)
  · exact hF.comp (by fun_prop)

/-- first coordinate on the unit sphere -/
noncomputable def c0 (u : sphere (0 : Space) 1) : ℝ := (u : Space).ofLp 0

lemma c0_meas : Measurable c0 := by
  unfold c0; fun_prop

/-- **Archimedes' hat-box theorem**: the first coordinate of a point on the unit sphere
is uniformly distributed on `[-1, 1]` (with total mass `4π`). -/
theorem archimedes :
    (volume : Measure Space).toSphere.map c0 =
      ENNReal.ofReal (2 * π) • volume.restrict (Set.Ioo (-1) 1) := by
  ext T hT
  rw [Measure.map_apply c0_meas hT, Measure.toSphere_apply' _ (c0_meas hT), finrank_euclideanSpace_fin,
    Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hT]
  set D : Set Space := {x | ‖x‖ ^ 2 < 1 ∧ x.ofLp 0 / ‖x‖ ∈ T} with hD
  have hC : Set.Ioo (0:ℝ) 1 • ((↑) '' (c0 ⁻¹' T) : Set Space) = D \ {0} := by
    ext x; constructor
    · rintro ⟨c, hc, y, ⟨u, hu, rfl⟩, rfl⟩
      have hu1 : ‖(u : Space)‖ = 1 := by simp
      have hn : ‖c • (u : Space)‖ = c := by rw [norm_smul, hu1, Real.norm_eq_abs, abs_of_pos hc.1, mul_one]
      refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [hn]; nlinarith [hc.1, hc.2]
      · show (c • (u : Space)).ofLp 0 / ‖c • (u : Space)‖ ∈ T
        rw [hn]; simp only [PiLp.smul_apply, smul_eq_mul]
        rw [mul_div_cancel_left₀ _ hc.1.ne']; exact hu
      · intro h0
        have h0' : c • (u : Space) = 0 := h0
        have : ‖c • (u : Space)‖ = 0 := by rw [h0']; simp
        rw [hn] at this; linarith [hc.1]
    · rintro ⟨⟨h1, h2⟩, h3⟩
      have hx0 : x ≠ 0 := h3
      have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx0
      have hn1 : ‖x‖ < 1 := by nlinarith [norm_nonneg x]
      refine ⟨‖x‖, ⟨hn, hn1⟩, ‖x‖⁻¹ • x, ⟨⟨‖x‖⁻¹ • x, by simp [norm_smul, hn.ne']⟩, ?_, rfl⟩, ?_⟩
      · show (‖x‖⁻¹ • x).ofLp 0 ∈ T
        simp only [PiLp.smul_apply, smul_eq_mul]
        rw [inv_mul_eq_div]; exact h2
      · simp only; rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
  rw [hC, measure_sdiff_null (measure_singleton 0)]
  have hDm : MeasurableSet D := by
    apply MeasurableSet.inter
    · exact measurableSet_lt (f := fun x : Space => ‖x‖ ^ 2) (by fun_prop) measurable_const
    · exact (by fun_prop : Measurable fun x : Space => x.ofLp 0 / ‖x‖) hT
  have hvol : volume D = ∫⁻ x : Space, (Set.Iio (1:ℝ)).indicator 1 (‖x‖ ^ 2) *
      T.indicator 1 (x.ofLp 0 / ‖x‖) := by
    rw [← lintegral_indicator_one hDm]
    congr 1; funext x
    by_cases ha : ‖x‖ ^ 2 < 1 <;> by_cases hb : x.ofLp 0 / ‖x‖ ∈ T <;>
      simp [hD, Set.indicator, ha, hb] <;> (try push Not at ha) <;> nlinarith [norm_nonneg x]
  rw [hvol, cone_lintegral _ (measurable_one.indicator hT), lintegral_indicator_one hT,
    Measure.restrict_apply hT]
  rw [← mul_assoc, mul_comm ((3:ℕ) : ℝ≥0∞), mul_assoc, ← mul_assoc ((3:ℕ) : ℝ≥0∞)]
  rw [show ((3:ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / 3) = 1 by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by norm_num)]; norm_num, one_mul]


/-- restriction of a linear isometry to the unit sphere -/
noncomputable def sph (A : Space ≃ₗᵢ[ℝ] Space) (u : sphere (0 : Space) 1) : sphere (0 : Space) 1 :=
  ⟨A u, by simp⟩

lemma sph_measurable (A : Space ≃ₗᵢ[ℝ] Space) : Measurable (sph A) :=
  (A.continuous.comp continuous_subtype_val).subtype_mk _ |>.measurable

lemma toSphere_map_sph (A : Space ≃ₗᵢ[ℝ] Space) :
    (volume : Measure Space).toSphere.map (sph A) = (volume : Measure Space).toSphere := by
  ext s hs
  rw [Measure.map_apply (sph_measurable A) hs,
    Measure.toSphere_apply' _ (sph_measurable A hs), Measure.toSphere_apply' _ hs]
  congr 1
  have h1 : ((↑) '' (sph A ⁻¹' s) : Set Space) = A ⁻¹' ((↑) '' s) := by
    ext x; constructor
    · rintro ⟨u, hu, rfl⟩; exact ⟨sph A u, hu, rfl⟩
    · rintro ⟨v, hv, hvx⟩
      refine ⟨⟨x, ?_⟩, ?_, rfl⟩
      · have : ‖A x‖ = 1 := by rw [← hvx]; simpa using v.2
        simpa using this
      · have : (sph A ⟨x, by have : ‖A x‖ = 1 := (by rw [← hvx]; simpa using v.2); simpa using this⟩) = v :=
          Subtype.ext hvx.symm
        show sph A _ ∈ s
        convert hv
  have h2 : Set.Ioo (0:ℝ) 1 • (A ⁻¹' ((↑) '' s : Set Space)) = A ⁻¹' (Set.Ioo (0:ℝ) 1 • ((↑) '' s)) := by
    ext x; constructor
    · rintro ⟨c, hc, y, hy, rfl⟩
      exact ⟨c, hc, A y, hy, by simp⟩
    · rintro ⟨c, hc, y, hy, hxy⟩
      refine ⟨c, hc, A.symm y, by simpa using hy, ?_⟩
      apply A.injective; simp [← hxy]
  rw [h1, h2]
  have hA : MeasurePreserving (A.toHomeomorph.toMeasurableEquiv) volume volume :=
    A.measurePreserving
  exact hA.measure_preimage_equiv _

noncomputable def e0 : Space := EuclideanSpace.single 0 1

lemma norm_e0 : ‖e0‖ = 1 := by simp [e0]

lemma exists_isom (v : Space) (hv : ‖v‖ = 1) : ∃ A : Space ≃ₗᵢ[ℝ] Space, A e0 = v :=
  ⟨Submodule.reflection (ℝ ∙ (e0 - v))ᗮ, Submodule.reflection_sub (by rw [norm_e0, hv])⟩

variable {μ : Measure Space}
noncomputable abbrev sig : Measure (sphere (0 : Space) 1) := (volume : Measure Space).toSphere

lemma sig_univ : sig Set.univ = ENNReal.ofReal (4 * π) := by
  have h := congrArg (fun m => m Set.univ) archimedes
  try simp only at h
  rw [Measure.map_apply c0_meas MeasurableSet.univ, Set.preimage_univ] at h
  rw [h, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    volume_Ioo, smul_eq_mul, ← ENNReal.ofReal_mul (by positivity)]
  congr 1; norm_num; ring

lemma sig_real_univ : sig.real Set.univ = 4 * π := by
  rw [measureReal_def, sig_univ, ENNReal.toReal_ofReal (by positivity)]

lemma arch_integral (f : ℝ → ℝ) (hf : Measurable f) :
    ∫ u, f (c0 u) ∂sig = 2 * π * ∫ t in Set.Ioo (-1) 1, f t := by
  rw [← integral_map c0_meas.aemeasurable hf.aestronglyMeasurable, archimedes,
    integral_smul_measure, ENNReal.toReal_ofReal (by positivity), smul_eq_mul]

lemma arch_integrable (f : ℝ → ℝ) (hf : Measurable f) (h : Integrable (fun u => f (c0 u)) sig) :
    IntegrableOn f (Set.Ioo (-1) 1) := by
  have h2 : Integrable f (sig.map c0) :=
    (integrable_map_measure hf.aestronglyMeasurable c0_meas.aemeasurable).mpr h
  rw [archimedes] at h2
  exact (integrable_smul_measure (by simp [pi_pos]) ENNReal.ofReal_ne_top).mp h2

noncomputable def sphEquiv (A : Space ≃ₗᵢ[ℝ] Space) : sphere (0 : Space) 1 ≃ᵐ sphere (0 : Space) 1 where
  toFun := sph A
  invFun := sph A.symm
  left_inv u := by ext1; simp [sph]
  right_inv u := by ext1; simp [sph]
  measurable_toFun := sph_measurable A
  measurable_invFun := sph_measurable A.symm

lemma sph_mp (A : Space ≃ₗᵢ[ℝ] Space) : MeasurePreserving (sphEquiv A) sig sig :=
  ⟨sph_measurable A, toSphere_map_sph A⟩

lemma sig_integral_isom {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Space ≃ₗᵢ[ℝ] Space) (f : sphere (0 : Space) 1 → E) :
    ∫ u, f (sph A u) ∂sig = ∫ u, f u ∂sig :=
  (sph_mp A).integral_comp' f

lemma sig_integrable_isom {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Space ≃ₗᵢ[ℝ] Space) (f : sphere (0 : Space) 1 → E) :
    Integrable (fun u => f (sph A u)) sig ↔ Integrable f sig :=
  (sph_mp A).integrable_comp_emb (sphEquiv A).measurableEmbedding

/-- the shell integrand, as a function of `t = ⟪u, e0⟫` -/
noncomputable def f0 (r s t : ℝ) : ℝ := (r - s * t) / (√(r ^ 2 - 2 * r * s * t + s ^ 2)) ^ 3

noncomputable def Phi (r s t : ℝ) : ℝ := (r * t - s) / (r ^ 2 * √(r ^ 2 - 2 * r * s * t + s ^ 2))

lemma D_pos (r s t : ℝ) (hr : 0 < r) (hs : 0 ≤ s) (hrs : s ≠ r) (ht : t ≤ 1) :
    0 < r ^ 2 - 2 * r * s * t + s ^ 2 := by
  have h1 : 0 < (r - s) ^ 2 := by
    have : r - s ≠ 0 := sub_ne_zero.mpr (Ne.symm hrs)
    positivity
  nlinarith [mul_nonneg (mul_nonneg hr.le hs) (sub_nonneg.mpr ht)]

lemma Phi_deriv (r s t : ℝ) (hr : 0 < r) (hD : 0 < r ^ 2 - 2 * r * s * t + s ^ 2) :
    HasDerivAt (Phi r s) (f0 r s t) t := by
  have hD' := hD.ne'
  have h1 : HasDerivAt (fun t => r ^ 2 - 2 * r * s * t + s ^ 2) (-(2 * r * s)) t := by
    have := ((hasDerivAt_id t).const_mul (2 * r * s)).const_sub (r ^ 2) |>.add_const (s ^ 2)
    simpa using this
  have h2 := h1.sqrt hD'
  have h3 := (h2.const_mul (r ^ 2))
  have h4 : HasDerivAt (fun t => r * t - s) r t := by
    simpa using ((hasDerivAt_id t).const_mul r).sub_const s
  have hsq : 0 < √(r ^ 2 - 2 * r * s * t + s ^ 2) := sqrt_pos.mpr hD
  have h5 := h4.div h3 (by positivity)
  refine HasDerivAt.congr_deriv
    (f := fun t => (r * t - s) / (r ^ 2 * √(r ^ 2 - 2 * r * s * t + s ^ 2))) h5 ?_
  unfold f0
  have hss : √(r ^ 2 - 2 * r * s * t + s ^ 2) ^ 2 = r ^ 2 - 2 * r * s * t + s ^ 2 := sq_sqrt hD.le
  generalize √(r ^ 2 - 2 * r * s * t + s ^ 2) = q at hss hsq ⊢
  field_simp
  rw [hss]
  ring

lemma shell_ftc (r s : ℝ) (hr : 0 < r) (hs : 0 ≤ s) (hrs : s ≠ r) :
    ∫ t in Set.Ioo (-1) 1, f0 r s t = if s < r then 2 / r ^ 2 else 0 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num)]
  have hD : ∀ t ∈ Set.uIcc (-1:ℝ) 1, 0 < r ^ 2 - 2 * r * s * t + s ^ 2 := by
    intro t ht
    rw [Set.uIcc_of_le (by norm_num)] at ht
    exact D_pos r s t hr hs hrs ht.2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => Phi_deriv r s t hr (hD t ht))]
  · unfold Phi
    have e1 : r ^ 2 - 2 * r * s * 1 + s ^ 2 = (r - s) ^ 2 := by ring
    have e2 : r ^ 2 - 2 * r * s * (-1) + s ^ 2 = (r + s) ^ 2 := by ring
    rw [e1, e2, sqrt_sq_eq_abs, sqrt_sq_eq_abs, abs_of_pos (by linarith : 0 < r + s)]
    split_ifs with h
    · rw [abs_of_pos (by linarith : 0 < r - s)]
      field_simp; ring
    · have : s > r := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hrs)
      rw [abs_of_neg (by linarith : r - s < 0)]
      field_simp; ring
  · apply ContinuousOn.intervalIntegrable
    intro t ht
    apply ContinuousAt.continuousWithinAt
    unfold f0
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    exact pow_ne_zero 3 (sqrt_pos.mpr (hD t ht)).ne'

lemma inner_e0 (v : Space) : ⟪e0, v⟫ = v.ofLp 0 := by
  simp [e0, EuclideanSpace.inner_single_left]

noncomputable def K (z : Space) : Space := (‖z‖ ^ 3)⁻¹ • z

lemma K_meas : Measurable K := by unfold K; fun_prop

lemma K_isom (A : Space ≃ₗᵢ[ℝ] Space) (z : Space) : K (A z) = A (K z) := by
  simp [K, map_smul]

lemma inner_K_e0 (r s : ℝ) (u : sphere (0 : Space) 1) :
    ⟪K (r • (u : Space) - s • e0), (u : Space)⟫ = f0 r s (c0 u) := by
  have hu : ‖(u : Space)‖ = 1 := by simp
  have huu : ⟪(u : Space), (u : Space)⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hn : ‖r • (u : Space) - s • e0‖ = √(r ^ 2 - 2 * r * s * c0 u + s ^ 2) := by
    rw [← sqrt_sq (norm_nonneg _), norm_sub_sq_real, norm_smul, norm_smul, inner_smul_left,
      inner_smul_right, hu, norm_e0, real_inner_comm, inner_e0]
    simp only [Real.norm_eq_abs, conj_trivial, c0]
    congr 1; rw [mul_pow, mul_pow, sq_abs, sq_abs]; ring
  rw [K, inner_smul_left, hn, inner_sub_left, inner_smul_left, inner_smul_left, huu, inner_e0]
  simp only [conj_trivial, f0, c0]
  field_simp

lemma f0_meas (r s : ℝ) : Measurable (f0 r s) := by unfold f0; fun_prop

lemma exists_isom_of (y : Space) : ∃ A : Space ≃ₗᵢ[ℝ] Space, y = ‖y‖ • A e0 := by
  rcases eq_or_ne y 0 with rfl | hy
  · exact ⟨LinearIsometryEquiv.refl ℝ Space, by simp⟩
  · have hn : 0 < ‖y‖ := norm_pos_iff.mpr hy
    obtain ⟨A, hA⟩ := exists_isom (‖y‖⁻¹ • y) (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne'])
    exact ⟨A, by rw [hA, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]⟩

lemma rotate_to_e0 (r : ℝ) (y : Space) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Space → Space → E) (hF : ∀ (A : Space ≃ₗᵢ[ℝ] Space) z u, F (A z) (A u) = F z u) :
    ∫ u, F (r • (u : Space) - y) u ∂sig = ∫ u, F (r • (u : Space) - ‖y‖ • e0) u ∂sig := by
  obtain ⟨A, hA⟩ := exists_isom_of y
  rw [← sig_integral_isom A]
  congr 1; funext u
  have : r • ((sph A u : sphere (0 : Space) 1) : Space) - y = A (r • (u : Space) - ‖y‖ • e0) := by
    conv_lhs => rw [hA]
    simp [sph, map_sub, map_smul]
  rw [this]
  exact hF A _ _

/-- Gauss flux of the point-source field through a sphere of radius `r` -/
lemma shell_K (r : ℝ) (hr : 0 < r) (y : Space) (hy : ‖y‖ ≠ r) :
    ∫ u, ⟪K (r • (u : Space) - y), (u : Space)⟫ ∂sig = if ‖y‖ < r then 4 * π / r ^ 2 else 0 := by
  rw [rotate_to_e0 r y (fun z u => ⟪K z, u⟫) (fun A z u => by simp [K_isom])]
  simp_rw [inner_K_e0]
  rw [arch_integral _ (f0_meas r ‖y‖), shell_ftc r ‖y‖ hr (norm_nonneg y) hy]
  split_ifs
  · field_simp; norm_num
  · simp

end PenAux


open MeasureTheory Metric Real Set
open scoped ENNReal RealInnerProductSpace

namespace PenAux

lemma finrank_sub : Module.finrank ℝ Space - 1 = 2 := by simp

noncomputable abbrev nu : Measure (Ioi (0:ℝ)) := Measure.volumeIoiPow 2

lemma polar_mp : MeasurePreserving (homeomorphUnitSphereProd Space)
    ((volume : Measure Space).comap (↑)) (sig.prod nu) := by
  have := (volume : Measure Space).measurePreserving_homeomorphUnitSphereProd
  rw [finrank_sub] at this
  exact this

lemma polar_integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Space → F) :
    ∫ x, f x = ∫ p : sphere (0:Space) 1 × Ioi (0:ℝ), f (p.2.1 • (p.1 : Space)) ∂(sig.prod nu) := by
  calc ∫ x, f x = ∫ x : ({(0:Space)}ᶜ : Set Space), f x.1 ∂((volume : Measure Space).comap Subtype.val) := by
        rw [integral_subtype_comap (measurableSet_singleton _).compl f, restrict_compl_singleton]
    _ = _ := by
        rw [← polar_mp.integral_comp (Homeomorph.measurableEmbedding _)]
        congr 1; funext x
        congr 1
        have : (x : Space) ≠ 0 := x.2
        have : 0 < ‖(x : Space)‖ := norm_pos_iff.mpr this
        simp [smul_smul, this.ne']

lemma polar_integrable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Space → F)
    (hf : Integrable f) :
    Integrable (fun p : sphere (0:Space) 1 × Ioi (0:ℝ) => f (p.2.1 • (p.1 : Space))) (sig.prod nu) := by
  have h1 : Integrable (fun x : ({(0:Space)}ᶜ : Set Space) => f x.1) ((volume : Measure Space).comap Subtype.val) := by
    have := (integrableOn_iff_comap_subtypeVal (f := f) (μ := volume)
      (measurableSet_singleton (0:Space)).compl).mp hf.integrableOn
    exact this
  rw [← polar_mp.integrable_comp_emb (Homeomorph.measurableEmbedding _)]
  refine h1.congr (Filter.Eventually.of_forall fun x => ?_)
  have : (x : Space) ≠ 0 := x.2
  have : 0 < ‖(x : Space)‖ := norm_pos_iff.mpr this
  simp [smul_smul, this.ne']

lemma nu_integral {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (g : ℝ → F) :
    ∫ r, g r.1 ∂nu = ∫ r in Ioi (0:ℝ), r ^ 2 • g r := by
  simp only [nu, Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul,
    integral_subtype_comap measurableSet_Ioi fun a ↦ Real.toNNReal (a ^ 2) • g a,
    setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_]
  · rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hx.out.le _)]
  · exact (measurable_subtype_coe.pow_const _).real_toNNReal

noncomputable def hk (d s : ℝ) : ℝ := (s ^ 2 * max s d ^ 2)⁻¹

lemma hk_nonneg (d s : ℝ) : 0 ≤ hk d s := by unfold hk; positivity

lemma prod_le_hk_aux (a b d : ℝ) (ha : 0 ≤ a) (hd : 0 < d) (h : 2 * d ≤ a + b) (hab : a ≤ b) :
    (a ^ 2 * b ^ 2)⁻¹ ≤ hk d a + hk d b := by
  have hb' : max a d ≤ b := max_le hab (by linarith)
  have : (a ^ 2 * b ^ 2)⁻¹ ≤ hk d a := by
    unfold hk
    rcases eq_or_lt_of_le ha with h0 | h0
    · subst h0; simp
    · have h1 : 0 < max a d := lt_max_of_lt_right hd
      apply inv_anti₀ (by positivity)
      gcongr
  linarith [hk_nonneg d b]

lemma prod_le_hk (a b d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 < d) (h : 2 * d ≤ a + b) :
    (a ^ 2 * b ^ 2)⁻¹ ≤ hk d a + hk d b := by
  rcases le_total a b with hab | hab
  · exact prod_le_hk_aux a b d ha hd h hab
  · have := prod_le_hk_aux b a d hb hd (by linarith) hab
    rw [mul_comm]; linarith

lemma rad_integrableOn (d : ℝ) (hd : 0 < d) : IntegrableOn (fun y : ℝ => (max y d ^ 2)⁻¹) (Ioi 0) := by
  have hU : Ioi (0:ℝ) = Ioc 0 d ∪ Ioi d := (Ioc_union_Ioi_eq_Ioi hd.le).symm
  rw [hU]
  refine IntegrableOn.union ?_ ?_
  · refine (integrableOn_const (C := (d ^ 2)⁻¹) (by simp)).congr_fun (fun y hy => ?_) measurableSet_Ioc
    simp [max_eq_right hy.2]
  · have := integrableOn_Ioi_rpow_of_lt (a := (-2:ℝ)) (by norm_num) hd
    refine this.congr_fun (fun y hy => ?_) measurableSet_Ioi
    have hy' : d < y := hy
    simp only
    rw [max_eq_left hy'.le, rpow_neg (by linarith), rpow_two]

lemma rad_integral (d : ℝ) (hd : 0 < d) : ∫ y in Ioi (0:ℝ), (max y d ^ 2)⁻¹ = 2 / d := by
  have hU : Ioi (0:ℝ) = Ioc 0 d ∪ Ioi d := (Ioc_union_Ioi_eq_Ioi hd.le).symm
  have hi := rad_integrableOn d hd
  rw [hU] at hi ⊢
  rw [setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi (hi.mono_set subset_union_left)
    (hi.mono_set subset_union_right)]
  have h1 : ∫ y in Ioc 0 d, (max y d ^ 2)⁻¹ = d * (d ^ 2)⁻¹ := by
    rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ => (d ^ 2)⁻¹) (fun y hy => by
      simp [max_eq_right hy.2])]
    simp [hd.le]
  have h2 : ∫ y in Ioi d, (max y d ^ 2)⁻¹ = d⁻¹ := by
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun y => y ^ (-2:ℝ)) (fun y hy => by
      have hy' : d < y := hy
      simp only
      rw [max_eq_left hy'.le, rpow_neg (by linarith), rpow_two])]
    rw [integral_Ioi_rpow_of_lt (by norm_num) hd]
    norm_num
    rw [rpow_neg_one]
  rw [h1, h2]
  field_simp
  ring

noncomputable abbrev V : ℝ := (volume : Measure Space).real (ball 0 1)

lemma hk_integrable (d : ℝ) (hd : 0 < d) : Integrable (fun x : Space => hk d ‖x‖) := by
  rw [integrable_fun_norm_addHaar volume (f := hk d), finrank_sub]
  refine (rad_integrableOn d hd).congr_fun (fun y hy => ?_) measurableSet_Ioi
  have hy' : 0 < y := hy
  simp only [hk, smul_eq_mul]
  field_simp

lemma hk_integral (d : ℝ) (hd : 0 < d) : ∫ x : Space, hk d ‖x‖ = 6 * V / d := by
  rw [integral_fun_norm_addHaar volume (hk d), finrank_sub]
  rw [setIntegral_congr_fun measurableSet_Ioi (g := fun y => (max y d ^ 2)⁻¹) (fun y hy => by
    have hy' : 0 < y := hy
    simp only [hk, smul_eq_mul]
    field_simp), rad_integral d hd]
  simp [finrank_euclideanSpace_fin, V]
  ring

lemma kprod_meas (c : Space) : Measurable (fun u : Space => (‖u‖ ^ 2 * ‖u - c‖ ^ 2)⁻¹) := by
  fun_prop

lemma kprod_integrable (c : Space) (hc : c ≠ 0) :
    Integrable (fun u : Space => (‖u‖ ^ 2 * ‖u - c‖ ^ 2)⁻¹) := by
  have hd : 0 < ‖c‖ / 2 := by have := norm_pos_iff.mpr hc; linarith
  have hI := (hk_integrable _ hd).add ((hk_integrable _ hd).comp_sub_right c)
  refine hI.mono' (kprod_meas c).aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  apply prod_le_hk _ _ _ (norm_nonneg _) (norm_nonneg _) hd
  have := norm_sub_le_norm_sub_add_norm_sub c u 0
  simp only [sub_zero, zero_sub, norm_neg] at this
  rw [norm_sub_rev] at this
  linarith

lemma kprod_integral_le (c : Space) (hc : c ≠ 0) :
    ∫ u : Space, (‖u‖ ^ 2 * ‖u - c‖ ^ 2)⁻¹ ≤ 24 * V / ‖c‖ := by
  have hd : 0 < ‖c‖ / 2 := by have := norm_pos_iff.mpr hc; linarith
  have hI := (hk_integrable _ hd).add ((hk_integrable _ hd).comp_sub_right c)
  calc ∫ u : Space, (‖u‖ ^ 2 * ‖u - c‖ ^ 2)⁻¹
      ≤ ∫ u : Space, (hk (‖c‖ / 2) ‖u‖ + hk (‖c‖ / 2) ‖u - c‖) := by
        apply integral_mono (kprod_integrable c hc) hI
        intro u
        apply prod_le_hk _ _ _ (norm_nonneg _) (norm_nonneg _) hd
        have := norm_sub_le_norm_sub_add_norm_sub c u 0
        simp only [sub_zero, zero_sub, norm_neg] at this
        rw [norm_sub_rev] at this
        linarith
    _ = 24 * V / ‖c‖ := by
        rw [integral_add (hk_integrable _ hd) ((hk_integrable _ hd).comp_sub_right c),
          integral_sub_right_eq_self (fun x : Space => hk (‖c‖ / 2) ‖x‖) c, hk_integral _ hd]
        field_simp
        ring

end PenAux


open MeasureTheory Metric Real Set
open scoped ENNReal RealInnerProductSpace

namespace PenAux

lemma norm_K (z : Space) : ‖K z‖ = (‖z‖ ^ 2)⁻¹ := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [K]
  have hn := norm_pos_iff.mpr hz
  rw [K, norm_smul, norm_inv, norm_pow, norm_norm]
  field_simp

lemma Jint_bound (c u : Space) : ‖⟪K u, K (u - c)⟫‖ ≤ (‖u‖ ^ 2 * ‖u - c‖ ^ 2)⁻¹ := by
  rw [Real.norm_eq_abs]
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [norm_K, norm_K, mul_inv]

lemma J_meas (c : Space) : Measurable (fun u : Space => ⟪K u, K (u - c)⟫) :=
  K_meas.inner (K_meas.comp (measurable_id.sub_const c))

lemma J_integrable (c : Space) (hc : c ≠ 0) : Integrable (fun u : Space => ⟪K u, K (u - c)⟫) :=
  (kprod_integrable c hc).mono' (J_meas c).aestronglyMeasurable
    (Filter.Eventually.of_forall (Jint_bound c))

lemma K_smul (r : ℝ) (hr : 0 < r) (ω : sphere (0:Space) 1) :
    K (r • (ω : Space)) = (r ^ 2)⁻¹ • (ω : Space) := by
  have hω : ‖(ω : Space)‖ = 1 := by simp
  rw [K, norm_smul, hω, Real.norm_eq_abs, abs_of_pos hr, smul_smul]
  congr 1
  field_simp

lemma nu_ae_ne (a : ℝ) : ∀ᵐ r ∂nu, r.1 ≠ a := by
  have hac : nu ≪ (volume : Measure ℝ).comap (Subtype.val : Ioi (0:ℝ) → ℝ) :=
    withDensity_absolutelyContinuous _ _
  refine hac.ae_le ?_
  show ∀ᵐ r ∂((volume : Measure ℝ).comap (Subtype.val : Ioi (0:ℝ) → ℝ)), r.1 ≠ a
  rw [ae_iff]
  have : {x : Ioi (0:ℝ) | ¬ (x.1 ≠ a)} = Subtype.val ⁻¹' {a} := by
    ext x; simp
  rw [this, comap_subtype_coe_apply measurableSet_Ioi]
  apply measure_mono_null (t := {a}) _ (measure_singleton a)
  · rintro _ ⟨r, hr, rfl⟩
    exact hr

theorem J_eq (c : Space) (hc : c ≠ 0) : ∫ u, ⟪K u, K (u - c)⟫ = 4 * π / ‖c‖ := by
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  rw [polar_integral]
  have hi := polar_integrable _ (J_integrable c hc)
  rw [integral_prod_symm _ hi]
  have hin : ∀ᵐ r ∂nu, ∫ ω, ⟪K (r.1 • (ω : Space)), K (r.1 • (ω : Space) - c)⟫ ∂sig =
      (fun s : ℝ => (s ^ 2)⁻¹ * if ‖c‖ < s then 4 * π / s ^ 2 else 0) r.1 := by
    filter_upwards [nu_ae_ne ‖c‖] with r hr
    have hr0 : 0 < r.1 := r.2
    simp_rw [K_smul r.1 hr0, inner_smul_left, conj_trivial]
    rw [integral_const_mul]
    have : ∀ ω : sphere (0:Space) 1, ⟪(ω : Space), K (r.1 • (ω : Space) - c)⟫ =
        ⟪K (r.1 • (ω : Space) - c), (ω : Space)⟫ := fun ω => real_inner_comm _ _
    simp_rw [this]
    rw [shell_K r.1 hr0 c (Ne.symm hr)]
  rw [integral_congr_ae hin, nu_integral (fun s : ℝ => (s ^ 2)⁻¹ * if ‖c‖ < s then 4 * π / s ^ 2 else 0)]
  have h2 : ∀ r ∈ Ioi (0:ℝ), r ^ 2 • ((r ^ 2)⁻¹ * if ‖c‖ < r then 4 * π / r ^ 2 else 0) =
      (Ioi ‖c‖).indicator (fun r => 4 * π * r ^ (-2:ℝ)) r := by
    intro r hr
    have hr' : 0 < r := hr
    simp only [smul_eq_mul, indicator, mem_Ioi]
    split_ifs
    · rw [rpow_neg hr'.le, rpow_two]; field_simp
    · simp
  rw [setIntegral_congr_fun measurableSet_Ioi h2, integral_indicator measurableSet_Ioi,
    Measure.restrict_restrict measurableSet_Ioi, Ioi_inter_Ioi, max_eq_left hcn.le,
    integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hcn]
  norm_num
  rw [rpow_neg_one]
  field_simp

end PenAux


open MeasureTheory Metric Real Set
open scoped ENNReal RealInnerProductSpace

namespace PenAux

set_option linter.unusedSectionVars false

lemma psi_ball_integrable (k : ℕ) (hk : k ≤ 2) :
    IntegrableOn (fun z : Space => (‖z‖ ^ k)⁻¹) (ball 0 1) := by
  rw [integrableOn_fun_norm_addHaar volume (f := fun s => (s ^ k)⁻¹), finrank_sub]
  have : IntegrableOn (fun y : ℝ => y ^ (2 - k)) (Ioo 0 1) :=
    (continuous_pow _).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  refine this.congr_fun (fun y hy => ?_) measurableSet_Ioo
  have hy' : 0 < y := hy.1
  simp only [smul_eq_mul]
  have : y ^ 2 = y ^ (2 - k) * y ^ k := by rw [← pow_add]; congr 1; omega
  rw [this]
  field_simp

section
variable (σ : Space → ℝ) (hσc : Continuous σ) (B : ℝ) (hB : ∀ y, |σ y| ≤ B)
  (hσi : Integrable σ)
include hσc hB hσi

lemma conv_bound (k : ℕ) (x y : Space) :
    |σ y| * (‖x - y‖ ^ k)⁻¹ ≤
      B * (ball (0:Space) 1).indicator (fun z => (‖z‖ ^ k)⁻¹) (x - y) + |σ y| := by
  by_cases h : ‖x - y‖ < 1
  · rw [indicator_of_mem (mem_ball_zero_iff.mpr h)]
    have := mul_le_mul_of_nonneg_right (hB y) (by positivity : (0:ℝ) ≤ (‖x - y‖ ^ k)⁻¹)
    linarith [abs_nonneg (σ y)]
  · rw [indicator_of_notMem (fun h' => h (mem_ball_zero_iff.mp h')), mul_zero, zero_add]
    have h1 : 1 ≤ ‖x - y‖ ^ k := one_le_pow₀ (not_lt.mp h)
    have h2 : (‖x - y‖ ^ k)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
    have := mul_le_mul_of_nonneg_left h2 (abs_nonneg (σ y))
    linarith

lemma conv_dom_integrable (k : ℕ) (hk : k ≤ 2) (x : Space) :
    Integrable (fun y => B * (ball (0:Space) 1).indicator (fun z => (‖z‖ ^ k)⁻¹) (x - y) + |σ y|) := by
  have h1 := ((psi_ball_integrable k hk).integrable_indicator measurableSet_ball).comp_sub_left x
  exact (h1.const_mul B).add hσi.abs

lemma conv_integrable (k : ℕ) (hk : k ≤ 2) (x : Space) :
    Integrable (fun y => |σ y| * (‖x - y‖ ^ k)⁻¹) := by
  refine (conv_dom_integrable σ hσc B hB hσi k hk x).mono'
    (by have := hσc.measurable; fun_prop) (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact conv_bound σ hσc B hB hσi k x y

lemma conv_integral_le (k : ℕ) (hk : k ≤ 2) (x : Space) :
    ∫ y, |σ y| * (‖x - y‖ ^ k)⁻¹ ≤
      B * (∫ z in ball (0:Space) 1, (‖z‖ ^ k)⁻¹) + ∫ y, |σ y| := by
  calc ∫ y, |σ y| * (‖x - y‖ ^ k)⁻¹
      ≤ ∫ y, (B * (ball (0:Space) 1).indicator (fun z => (‖z‖ ^ k)⁻¹) (x - y) + |σ y|) :=
        integral_mono (conv_integrable σ hσc B hB hσi k hk x)
          (conv_dom_integrable σ hσc B hB hσi k hk x) (conv_bound σ hσc B hB hσi k x)
    _ = _ := by
        have h1 := ((psi_ball_integrable k hk).integrable_indicator measurableSet_ball).comp_sub_left x
        rw [integral_add (h1.const_mul B) hσi.abs, integral_const_mul,
          integral_sub_left_eq_self (fun z => (ball (0:Space) 1).indicator (fun z => (‖z‖ ^ k)⁻¹) z),
          integral_indicator measurableSet_ball]

/-- the vector field integrand is integrable -/
lemma field_integrable (x : Space) : Integrable (fun y => σ y • K (x - y)) := by
  refine (conv_integrable σ hσc B hB hσi 2 le_rfl x).congr' ?_ ?_
  · have := hσc.measurable
    exact (this.smul (K_meas.comp (measurable_const.sub measurable_id))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y => by
      simp only [norm_smul, norm_K, Real.norm_eq_abs, abs_mul, abs_abs, abs_inv, abs_pow, abs_norm]

omit hσc hB hσi in
lemma diag_ae : ∀ᵐ q ∂((volume : Measure Space).prod volume), q.1 ≠ q.2 := by
  rw [Measure.ae_prod_iff_ae_ae]
  · refine Filter.Eventually.of_forall fun y => ?_
    rw [ae_iff]
    simp only [ne_eq, not_not]
    have : {x : Space | y = x} = {y} := by ext; simp [eq_comm]
    rw [this, measure_singleton]
  · exact (measurableSet_diagonal (α := Space)).compl

noncomputable def H0 (q : Space × Space) : ℝ := |σ q.1| * |σ q.2| * (‖q.1 - q.2‖ ^ 1)⁻¹

omit hσi hB in
lemma H0_meas : Measurable (H0 σ) := by
  have := hσc.measurable
  unfold H0; fun_prop

lemma H0_integrable : Integrable (H0 σ) ((volume : Measure Space).prod volume) := by
  rw [integrable_prod_iff (H0_meas σ hσc).aestronglyMeasurable]
  constructor
  · refine Filter.Eventually.of_forall fun y => ?_
    simp only [H0, mul_assoc]
    exact (conv_integrable σ hσc B hB hσi 1 (by norm_num) y).const_mul _
  · refine (hσi.abs.mul_const (B * (∫ z in ball (0:Space) 1, (‖z‖ ^ 1)⁻¹) + ∫ y, |σ y|)).mono' ?_ ?_
    · exact ((H0_meas σ hσc).norm.stronglyMeasurable.integral_prod_right' (f := fun q => ‖H0 σ q‖)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun y => ?_
      simp only [H0, mul_assoc, norm_mul, Real.norm_eq_abs, abs_abs]
      rw [abs_of_nonneg (integral_nonneg fun _ => by positivity)]
      rw [integral_const_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have := conv_integral_le σ hσc B hB hσi 1 (by norm_num) y
      refine le_trans (le_of_eq ?_) this
      congr 1; funext y'
      simp only [abs_mul, abs_abs, abs_inv, abs_pow, abs_norm]

end

lemma inner_K_le (a b : Space) : |⟪K a, K b⟫| ≤ (‖a‖ ^ 2 * ‖b‖ ^ 2)⁻¹ := by
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [norm_K, norm_K, mul_inv]

section
variable (σ : Space → ℝ) (hσc : Continuous σ) (B : ℝ) (hB : ∀ y, |σ y| ≤ B)
  (hσi : Integrable σ)
include hσc hB hσi

noncomputable def Fp (p : (Space × Space) × Space) : ℝ :=
  σ p.1.1 * σ p.1.2 * ⟪K (p.2 - p.1.1), K (p.2 - p.1.2)⟫

omit hB hσi in
lemma Fp_meas : Measurable (Fp σ) := by
  have := hσc.measurable
  unfold Fp
  exact ((this.comp measurable_fst.fst).mul (this.comp measurable_fst.snd)).mul
    ((K_meas.comp (measurable_snd.sub measurable_fst.fst)).inner
      (K_meas.comp (measurable_snd.sub measurable_fst.snd)))

omit hσc hB hσi in
lemma Fp_fiber (q : Space × Space) (hq : q.1 ≠ q.2) :
    Integrable (fun x => Fp σ (q, x)) ∧
    ∫ x, Fp σ (q, x) = 4 * π * (σ q.1 * σ q.2 / ‖q.1 - q.2‖) ∧
    ∫ x, ‖Fp σ (q, x)‖ ≤ 24 * V * H0 σ q := by
  obtain ⟨y, y'⟩ := q
  simp only at hq
  have hc : y' - y ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  have hshift : ∀ x : Space, ⟪K (x - y), K (x - y')⟫ =
      (fun u => ⟪K u, K (u - (y' - y))⟫) (x - y) := by
    intro x; simp only [sub_sub_sub_cancel_right]
  have hJi : Integrable (fun x => ⟪K (x - y), K (x - y')⟫) := by
    simp_rw [hshift]; exact (J_integrable _ hc).comp_sub_right y
  have hPi : Integrable (fun x : Space => (‖x - y‖ ^ 2 * ‖x - y'‖ ^ 2)⁻¹) := by
    have := (kprod_integrable _ hc).comp_sub_right y
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [sub_sub_sub_cancel_right]
  have hPI : ∫ x : Space, (‖x - y‖ ^ 2 * ‖x - y'‖ ^ 2)⁻¹ ≤ 24 * V / ‖y' - y‖ := by
    have := kprod_integral_le _ hc
    rw [← integral_sub_right_eq_self _ y] at this
    simpa only [sub_sub_sub_cancel_right] using this
  refine ⟨?_, ?_, ?_⟩
  · show Integrable (fun x => σ y * σ y' * ⟪K (x - y), K (x - y')⟫)
    exact hJi.const_mul _
  · simp only [Fp]
    rw [integral_const_mul]
    simp_rw [hshift]
    rw [integral_sub_right_eq_self (fun u => ⟪K u, K (u - (y' - y))⟫) y, J_eq _ hc, norm_sub_rev]
    ring
  · calc ∫ x, ‖Fp σ ((y, y'), x)‖ ≤ ∫ x, |σ y| * |σ y'| * (‖x - y‖ ^ 2 * ‖x - y'‖ ^ 2)⁻¹ := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
            (hPi.const_mul _) (Filter.Eventually.of_forall fun x => ?_)
          simp only [Fp, norm_mul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (inner_K_le _ _) (by positivity)
      _ = |σ y| * |σ y'| * ∫ x, (‖x - y‖ ^ 2 * ‖x - y'‖ ^ 2)⁻¹ := integral_const_mul _ _
      _ ≤ |σ y| * |σ y'| * (24 * V / ‖y' - y‖) := by gcongr
      _ = 24 * V * H0 σ (y, y') := by
          simp only [H0, pow_one]; rw [norm_sub_rev]; ring

lemma Fp_integrable :
    Integrable (Fp σ) (((volume : Measure Space).prod (volume : Measure Space)).prod volume) := by
  rw [integrable_prod_iff (Fp_meas σ hσc).aestronglyMeasurable]
  constructor
  · filter_upwards [diag_ae] with q hq
    exact (Fp_fiber σ q hq).1
  · refine ((H0_integrable σ hσc B hB hσi).const_mul (24 * V)).mono' ?_ ?_
    · exact ((Fp_meas σ hσc).norm.stronglyMeasurable.integral_prod_right'
        (f := fun p => ‖Fp σ p‖)).aestronglyMeasurable
    · filter_upwards [diag_ae] with q hq
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact (Fp_fiber σ q hq).2.2

lemma pair_integrable :
    Integrable (fun q : Space × Space => σ q.1 * σ q.2 / ‖q.1 - q.2‖)
      ((volume : Measure Space).prod volume) := by
  refine (H0_integrable σ hσc B hB hσi).mono' ?_ (Filter.Eventually.of_forall fun q => ?_)
  · have := hσc.measurable
    exact (by fun_prop : Measurable fun q : Space × Space => σ q.1 * σ q.2 / ‖q.1 - q.2‖).aestronglyMeasurable
  · simp only [H0, pow_one, Real.norm_eq_abs, abs_div, abs_mul, abs_norm, div_eq_mul_inv, abs_inv]
    rfl

theorem main_identity :
    ∫ x, ‖∫ y, σ y • K (x - y)‖ ^ 2 = 4 * π * ∫ y, ∫ y', σ y * σ y' / ‖y - y'‖ := by
  have hFi := Fp_integrable σ hσc B hB hσi
  have h1 : ∀ x, ‖∫ y, σ y • K (x - y)‖ ^ 2 = ∫ y, ∫ y', Fp σ ((y, y'), x) := by
    intro x
    have hfi := field_integrable σ hσc B hB hσi x
    rw [← real_inner_self_eq_norm_sq, ← integral_inner hfi]
    congr 1; funext y
    rw [inner_smul_right, real_inner_comm, ← integral_inner hfi, ← integral_const_mul]
    congr 1; funext y'
    rw [inner_smul_right]
    simp only [Fp]
    ring
  calc ∫ x, ‖∫ y, σ y • K (x - y)‖ ^ 2 = ∫ x, ∫ y, ∫ y', Fp σ ((y, y'), x) := integral_congr_ae
          (Filter.Eventually.of_forall h1)
    _ = ∫ x, ∫ q, Fp σ (q, x) ∂((volume : Measure Space).prod volume) := by
          refine integral_congr_ae ?_
          filter_upwards [hFi.prod_left_ae] with x hx
          exact (integral_prod (fun q => Fp σ (q, x)) hx).symm
    _ = ∫ q, ∫ x, Fp σ (q, x) ∂volume ∂((volume : Measure Space).prod volume) :=
          integral_integral_swap (f := fun x q => Fp σ (q, x)) hFi.swap
    _ = ∫ q, 4 * π * (σ q.1 * σ q.2 / ‖q.1 - q.2‖) ∂((volume : Measure Space).prod volume) := by
          refine integral_congr_ae ?_
          filter_upwards [diag_ae] with q hq
          exact (Fp_fiber σ q hq).2.1
    _ = 4 * π * ∫ y, ∫ y', σ y * σ y' / ‖y - y'‖ := by
          rw [integral_const_mul, integral_prod _ (pair_integrable σ hσc B hB hσi)]

end

end PenAux


open MeasureTheory Metric Real Set
open scoped ENNReal RealInnerProductSpace

namespace PenAux

set_option linter.unusedSectionVars false

abbrev SM := SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℝ

lemma sm_bound (σ : SM) : ∃ B, ∀ x, |σ x| ≤ B := ⟨‖σ.toBoundedContinuousFunction‖, fun x => by
  have := σ.toBoundedContinuousFunction.norm_coe_le_norm x
  simpa using this⟩

lemma pG_eq (G : ℝ) (ρ : SM) (x : Space) :
    Penrose.potentialGradient G ρ x = -G • ∫ y, ρ y • K (x - y) := by
  unfold Penrose.potentialGradient
  congr 2; funext y
  rw [K, smul_smul, div_eq_mul_inv]

lemma pG_sub (G : ℝ) (ρ ρ' : SM) (x : Space) :
    Penrose.potentialGradient G ρ x - Penrose.potentialGradient G ρ' x =
      -G • ∫ y, (ρ - ρ') y • K (x - y) := by
  obtain ⟨B, hB⟩ := sm_bound ρ
  obtain ⟨B', hB'⟩ := sm_bound ρ'
  rw [pG_eq, pG_eq, ← smul_sub, ← integral_sub (field_integrable _ ρ.continuous B hB ρ.integrable x)
    (field_integrable _ ρ'.continuous B' hB' ρ'.integrable x)]
  congr 2; funext y
  rw [SchwartzMap.sub_apply, sub_smul]

theorem core (G : ℝ) (ρ ρ' : SM) :
    Penrose.deltaMeasure G ρ ρ' =
      4 * π * G ^ 2 * ∫ x, ∫ y, (ρ x - ρ' x) * (ρ y - ρ' y) / ‖x - y‖ := by
  obtain ⟨B, hB⟩ := sm_bound (ρ - ρ')
  have h := main_identity (⇑(ρ - ρ')) (ρ - ρ').continuous B hB (ρ - ρ').integrable
  unfold Penrose.deltaMeasure
  simp_rw [pG_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [integral_const_mul]
  rw [h]
  simp only [SchwartzMap.sub_apply]
  ring

end PenAux


open MeasureTheory Metric Real Set
open scoped ENNReal RealInnerProductSpace

namespace PenAux

set_option linter.unusedSectionVars false

lemma conv1_integrable (ρ : SM) (x : Space) : Integrable (fun y => ρ y / ‖x - y‖) := by
  obtain ⟨B, hB⟩ := sm_bound ρ
  refine (conv_integrable (⇑ρ) ρ.continuous B hB ρ.integrable 1 (by norm_num) x).mono'
    (by
      have := ρ.continuous.measurable
      exact (by fun_prop : Measurable fun y => ρ y / ‖x - y‖).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun y => ?_)
  simp [div_eq_mul_inv]

lemma conv1_bound (ρ : SM) : ∃ M, ∀ x, ∫ y, |ρ y| / ‖x - y‖ ≤ M := by
  obtain ⟨B, hB⟩ := sm_bound ρ
  refine ⟨B * (∫ z in ball (0:Space) 1, (‖z‖ ^ 1)⁻¹) + ∫ y, |ρ y|, fun x => ?_⟩
  have := conv_integral_le (⇑ρ) ρ.continuous B hB ρ.integrable 1 (by norm_num) x
  simpa [div_eq_mul_inv] using this

lemma pair2_integrable (σ τ : SM) :
    Integrable (fun q : Space × Space => σ q.1 * τ q.2 / ‖q.1 - q.2‖)
      ((volume : Measure Space).prod volume) := by
  have hm : Measurable (fun q : Space × Space => σ q.1 * τ q.2 / ‖q.1 - q.2‖) := by
    have := σ.continuous.measurable; have := τ.continuous.measurable; fun_prop
  obtain ⟨M, hM⟩ := conv1_bound τ
  rw [integrable_prod_iff hm.aestronglyMeasurable]
  constructor
  · refine Filter.Eventually.of_forall fun y => ?_
    simp only [mul_div_assoc]
    exact (conv1_integrable τ y).const_mul _
  · refine (σ.integrable.abs.mul_const M).mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact (hm.norm.stronglyMeasurable.integral_prod_right'
        (f := fun q => ‖σ q.1 * τ q.2 / ‖q.1 - q.2‖‖)).aestronglyMeasurable
    · simp only [Real.norm_eq_abs, abs_div, abs_mul, abs_norm]
      rw [abs_of_nonneg (integral_nonneg fun _ => by positivity)]
      simp only [mul_div_assoc]
      rw [integral_const_mul]
      exact mul_le_mul_of_nonneg_left (hM y) (abs_nonneg _)

noncomputable def A2 (σ τ : SM) : ℝ := ∫ x, ∫ y, σ x * τ y / ‖x - y‖

lemma A2_prod (σ τ : SM) : A2 σ τ = ∫ q, σ q.1 * τ q.2 / ‖q.1 - q.2‖ ∂((volume : Measure Space).prod volume) :=
  (integral_prod _ (pair2_integrable σ τ)).symm

lemma A2_symm (σ τ : SM) : A2 τ σ = A2 σ τ := by
  rw [A2_prod, A2_prod, ← integral_prod_swap]
  congr 1; funext q
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [norm_sub_rev]; ring

lemma expand (ρ ρ' : SM) :
    ∫ x, ∫ y, (ρ x - ρ' x) * (ρ y - ρ' y) / ‖x - y‖ =
      A2 ρ ρ - A2 ρ ρ' - A2 ρ' ρ + A2 ρ' ρ' := by
  have h := A2_prod (ρ - ρ') (ρ - ρ')
  rw [A2] at h
  simp only [SchwartzMap.sub_apply] at h
  rw [h, A2_prod, A2_prod, A2_prod, A2_prod]
  have e : (fun q : Space × Space => (ρ q.1 - ρ' q.1) * (ρ q.2 - ρ' q.2) / ‖q.1 - q.2‖) =
      fun q => ((ρ q.1 * ρ q.2 / ‖q.1 - q.2‖ - ρ q.1 * ρ' q.2 / ‖q.1 - q.2‖)
        - ρ' q.1 * ρ q.2 / ‖q.1 - q.2‖) + ρ' q.1 * ρ' q.2 / ‖q.1 - q.2‖ := by
    funext q; ring
  have i1 : Integrable (fun q : Space × Space => ρ q.1 * ρ q.2 / ‖q.1 - q.2‖ - ρ q.1 * ρ' q.2 / ‖q.1 - q.2‖)
      ((volume : Measure Space).prod volume) := (pair2_integrable ρ ρ).sub (pair2_integrable ρ ρ')
  have i2 : Integrable (fun q : Space × Space => ρ q.1 * ρ q.2 / ‖q.1 - q.2‖ - ρ q.1 * ρ' q.2 / ‖q.1 - q.2‖
      - ρ' q.1 * ρ q.2 / ‖q.1 - q.2‖) ((volume : Measure Space).prod volume) :=
    i1.sub (pair2_integrable ρ' ρ)
  rw [e, integral_add i2 (pair2_integrable ρ' ρ'), integral_sub i1 (pair2_integrable ρ' ρ),
    integral_sub (pair2_integrable ρ ρ) (pair2_integrable ρ ρ')]

lemma pot_sub (G : ℝ) (ρ ρ' : SM) (x : Space) :
    Penrose.newtonianPotential G ρ x - Penrose.newtonianPotential G ρ' x =
      G * ∫ y, (ρ y - ρ' y) / ‖x - y‖ := by
  unfold Penrose.newtonianPotential
  rw [← mul_sub, ← integral_sub (conv1_integrable ρ x) (conv1_integrable ρ' x)]
  congr 2; funext y; ring

end PenAux


open MeasureTheory Metric Real Set Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace PenAux

set_option linter.unusedSectionVars false

/-! ### FTC along a segment for `‖w + s h‖⁻¹` -/

lemma norm_add_smul_sq (w h : Space) (s : ℝ) :
    ‖w + s • h‖ ^ 2 = ‖w‖ ^ 2 + 2 * s * ⟪w, h⟫ + s ^ 2 * ‖h‖ ^ 2 := by
  rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]; ring

lemma inv_norm_deriv (w h : Space) (s : ℝ) (hne : w + s • h ≠ 0) :
    HasDerivAt (fun s : ℝ => ‖w + s • h‖⁻¹) (-⟪K (w + s • h), h⟫) s := by
  have hq : ∀ t : ℝ, ‖w + t • h‖ = √(‖w‖ ^ 2 + 2 * t * ⟪w, h⟫ + t ^ 2 * ‖h‖ ^ 2) := by
    intro t; rw [← norm_add_smul_sq, sqrt_sq (norm_nonneg _)]
  simp_rw [hq]
  have hpos : 0 < ‖w‖ ^ 2 + 2 * s * ⟪w, h⟫ + s ^ 2 * ‖h‖ ^ 2 := by
    rw [← norm_add_smul_sq]; have := norm_pos_iff.mpr hne; positivity
  have h1 : HasDerivAt (fun t : ℝ => ‖w‖ ^ 2 + 2 * t * ⟪w, h⟫ + t ^ 2 * ‖h‖ ^ 2)
      (2 * ⟪w, h⟫ + 2 * s * ‖h‖ ^ 2) s := by
    have e := ((((hasDerivAt_id' s).const_mul 2).mul_const ⟪w, h⟫).const_add (‖w‖ ^ 2)).add
      ((hasDerivAt_pow 2 s).mul_const (‖h‖ ^ 2))
    exact e.congr_deriv (by simp)
  have h2 := (h1.sqrt hpos.ne').inv (sqrt_pos.mpr hpos).ne'
  refine h2.congr_deriv ?_
  unfold K
  rw [inner_smul_left, hq, inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq]
  simp only [conj_trivial]
  have hs := sq_sqrt hpos.le
  have hsp := sqrt_pos.mpr hpos
  generalize √(‖w‖ ^ 2 + 2 * s * ⟪w, h⟫ + s ^ 2 * ‖h‖ ^ 2) = q at hs hsp ⊢
  field_simp

lemma ftc_segment (w h : Space) (hne : ∀ s : ℝ, w + s • h ≠ 0) :
    ∫ s in (0:ℝ)..1, ⟪K (w + s • h), h⟫ = ‖w‖⁻¹ - ‖w + h‖⁻¹ := by
  have hd : ∀ s ∈ uIcc (0:ℝ) 1, HasDerivAt (fun s : ℝ => -‖w + s • h‖⁻¹) ⟪K (w + s • h), h⟫ s := by
    intro s _
    have e := (inv_norm_deriv w h s (hne s)).neg
    rw [neg_neg] at e
    exact e
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd]
  · simp; ring
  · apply ContinuousOn.intervalIntegrable
    intro s _
    apply ContinuousAt.continuousWithinAt
    unfold K
    have : ‖w + s • h‖ ≠ 0 := norm_ne_zero_iff.mpr (hne s)
    fun_prop (disch := positivity)

lemma line_null (x h : Space) : volume {y : Space | ∃ s : ℝ, y = x + s • h} = 0 := by
  have hS : (Submodule.span ℝ {h} : Submodule ℝ Space) ≠ ⊤ := by
    intro htop
    have h3 : Module.finrank ℝ (Submodule.span ℝ {h} : Submodule ℝ Space) = 3 := by
      rw [htop, finrank_top, finrank_euclideanSpace_fin]
    rcases eq_or_ne h 0 with rfl | hh
    · rw [Set.singleton_zero, Submodule.span_zero, finrank_bot] at h3; norm_num at h3
    · rw [finrank_span_singleton hh] at h3; norm_num at h3
  have h0 := Measure.addHaar_submodule volume _ hS
  have : {y : Space | ∃ s : ℝ, y = x + s • h} = (fun v => x + v) '' (Submodule.span ℝ {h} : Set Space) := by
    ext y; simp only [mem_setOf_eq, mem_image, SetLike.mem_coe, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨s, rfl⟩; exact ⟨s • h, ⟨s, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩; exact ⟨s, rfl⟩
  rw [this, image_add_left, measure_preimage_add]
  exact h0

end PenAux


open MeasureTheory Metric Real Set Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace PenAux

set_option linter.unusedSectionVars false

lemma pG_inner (G : ℝ) (ρ : SM) (x h : Space) :
    ⟪Penrose.potentialGradient G ρ x, h⟫ = -G * ∫ y, ρ y * ⟪K (x - y), h⟫ := by
  obtain ⟨B, hB⟩ := sm_bound ρ
  rw [pG_eq, inner_smul_left, real_inner_comm, ← integral_inner
    (field_integrable _ ρ.continuous B hB ρ.integrable x)]
  simp only [conj_trivial, inner_smul_right, real_inner_comm h]

lemma incr (G : ℝ) (ρ : SM) (x h : Space) :
    Penrose.newtonianPotential G ρ (x + h) - Penrose.newtonianPotential G ρ x =
      ∫ s in (0:ℝ)..1, ⟪Penrose.potentialGradient G ρ (x + s • h), h⟫ := by
  obtain ⟨B, hB⟩ := sm_bound ρ
  set P : ℝ × Space → ℝ := fun p => ρ p.2 * ⟪K (x + p.1 • h - p.2), h⟫ with hP
  have hPm : Measurable P := by
    have := ρ.continuous.measurable
    simp only [hP]
    exact (this.comp measurable_snd).mul
      ((K_meas.comp ((measurable_const.add (measurable_fst.smul_const h)).sub measurable_snd)).inner
        measurable_const)
  set M := B * (∫ z in ball (0:Space) 1, (‖z‖ ^ 2)⁻¹) + ∫ y, |ρ y| with hM
  have hfib : ∀ s : ℝ, Integrable (fun y => P (s, y)) ∧ ∫ y, ‖P (s, y)‖ ≤ M * ‖h‖ := by
    intro s
    have hc := conv_integrable (⇑ρ) ρ.continuous B hB ρ.integrable 2 le_rfl (x + s • h)
    have hle : ∀ y, ‖P (s, y)‖ ≤ |ρ y| * (‖x + s • h - y‖ ^ 2)⁻¹ * ‖h‖ := by
      intro y
      simp only [hP, norm_mul, Real.norm_eq_abs]
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      refine (abs_real_inner_le_norm _ _).trans ?_
      rw [norm_K]
    refine ⟨(hc.mul_const ‖h‖).mono' (hPm.comp measurable_prodMk_left).aestronglyMeasurable
      (Eventually.of_forall hle), ?_⟩
    calc ∫ y, ‖P (s, y)‖ ≤ ∫ y, |ρ y| * (‖x + s • h - y‖ ^ 2)⁻¹ * ‖h‖ :=
          integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) (hc.mul_const _)
            (Eventually.of_forall hle)
      _ = (∫ y, |ρ y| * (‖x + s • h - y‖ ^ 2)⁻¹) * ‖h‖ := integral_mul_const _ _
      _ ≤ M * ‖h‖ := by
          gcongr
          exact conv_integral_le (⇑ρ) ρ.continuous B hB ρ.integrable 2 le_rfl _
  have hPi : Integrable P ((volume.restrict (Ioc (0:ℝ) 1)).prod volume) := by
    rw [integrable_prod_iff hPm.aestronglyMeasurable]
    refine ⟨Eventually.of_forall fun s => (hfib s).1, ?_⟩
    refine (integrable_const (M * ‖h‖)).mono' ?_ (Eventually.of_forall fun s => ?_)
    · exact (hPm.norm.stronglyMeasurable.integral_prod_right' (f := fun p => ‖P p‖)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      exact (hfib s).2
  -- the right side
  have hR : ∫ s in (0:ℝ)..1, ⟪Penrose.potentialGradient G ρ (x + s • h), h⟫ =
      -G * ∫ y, ∫ s in Ioc (0:ℝ) 1, P (s, y) := by
    simp_rw [pG_inner]
    rw [intervalIntegral.integral_of_le zero_le_one, integral_const_mul]
    congr 1
    exact integral_integral_swap (f := fun s y => P (s, y)) hPi
  have hae : ∀ᵐ y ∂(volume : Measure Space), ∫ s in Ioc (0:ℝ) 1, P (s, y) =
      ρ y / ‖x - y‖ - ρ y / ‖x + h - y‖ := by
    have hnull := line_null x h
    rw [← compl_mem_ae_iff] at hnull
    filter_upwards [hnull] with y hy
    have hne : ∀ s : ℝ, (x - y) + s • h ≠ 0 := by
      intro s hs
      apply hy
      refine ⟨s, ?_⟩
      rw [sub_add_eq_add_sub, sub_eq_zero] at hs
      exact hs.symm
    simp only [hP]
    rw [integral_const_mul, ← intervalIntegral.integral_of_le zero_le_one]
    have : ∀ s : ℝ, x + s • h - y = (x - y) + s • h := fun s => by abel
    simp_rw [this]
    rw [ftc_segment _ _ hne]
    have : x - y + h = x + h - y := by abel
    rw [this]; ring
  rw [hR, integral_congr_ae hae, integral_sub (conv1_integrable ρ x) (conv1_integrable ρ (x + h))]
  unfold Penrose.newtonianPotential
  ring

end PenAux


open MeasureTheory Metric Real Set Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace PenAux

set_option linter.unusedSectionVars false

lemma sm_decay (ρ : SM) : ∃ C, ∀ w, |ρ w| ≤ C * ((1 + ‖w‖) ^ 4)⁻¹ := by
  refine ⟨2 ^ 4 * ((Finset.Iic ((4:ℕ), (0:ℕ))).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) ρ,
    fun w => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (4, 0)) le_rfl le_rfl ρ w
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  simp only at h
  have hp : 0 < (1 + ‖w‖) ^ 4 := by positivity
  rw [le_mul_inv_iff₀ hp]
  linarith [h, mul_comm ((1 + ‖w‖) ^ 4) |ρ w|]

lemma one_add_le (x x' z : Space) (hx : dist x' x < 1) :
    1 + ‖z‖ ≤ (1 + ‖x' - z‖) * (2 + ‖x‖) := by
  have h1 : ‖z‖ ≤ ‖x' - z‖ + ‖x'‖ := by
    have := norm_sub_le x' (x' - z)
    simp only [sub_sub_cancel] at this
    linarith [norm_sub_rev x' z]
  have h2 : ‖x'‖ ≤ ‖x‖ + 1 := by
    have := norm_le_norm_add_norm_sub' x' x
    rw [dist_eq_norm] at hx
    linarith
  nlinarith [norm_nonneg (x' - z), norm_nonneg x]

lemma conv_K_cont (ρ : SM) : Continuous (fun x : Space => ∫ z, ρ (x - z) • K z) := by
  obtain ⟨C, hC⟩ := sm_decay ρ
  rw [continuous_iff_continuousAt]
  intro x
  set C' := C * (2 + ‖x‖) ^ 4
  have hC0 : 0 ≤ C := by
    have := hC 0
    have h2 : 0 < ((1 + ‖(0:Space)‖) ^ 4)⁻¹ := by positivity
    nlinarith [abs_nonneg (ρ 0)]
  set bound : Space → ℝ := fun z =>
    C' * ((ball (0:Space) 1).indicator (fun z => (‖z‖ ^ 2)⁻¹) z + ((1 + ‖z‖) ^ 4)⁻¹)
  have hbi : Integrable bound := by
    refine Integrable.const_mul ?_ _
    refine ((psi_ball_integrable 2 le_rfl).integrable_indicator measurableSet_ball).add ?_
    have := integrable_one_add_norm (E := Space) (μ := volume) (r := 4) (by simp; norm_num)
    refine this.congr (Eventually.of_forall fun z => ?_)
    simp only
    rw [rpow_neg (by positivity)]
    norm_cast
  apply continuousAt_of_dominated (bound := bound)
  · refine Eventually.of_forall fun x' => ?_
    have := ρ.continuous.measurable
    exact ((this.comp (measurable_const.sub measurable_id)).smul K_meas).aestronglyMeasurable
  · filter_upwards [ball_mem_nhds x one_pos] with x' hx'
    refine Eventually.of_forall fun z => ?_
    rw [norm_smul, norm_K, Real.norm_eq_abs]
    have hd := one_add_le x x' z hx'
    have hρ := hC (x' - z)
    have hq : ((1 + ‖x' - z‖) ^ 4)⁻¹ ≤ (2 + ‖x‖) ^ 4 * ((1 + ‖z‖) ^ 4)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
      calc ((1 + ‖x' - z‖) ^ 4)⁻¹ * (1 + ‖z‖) ^ 4
          ≤ ((1 + ‖x' - z‖) ^ 4)⁻¹ * ((1 + ‖x' - z‖) * (2 + ‖x‖)) ^ 4 := by gcongr
        _ = (2 + ‖x‖) ^ 4 := by
            rw [mul_pow]; field_simp
    have hρ' : |ρ (x' - z)| ≤ C' * ((1 + ‖z‖) ^ 4)⁻¹ := by
      calc |ρ (x' - z)| ≤ C * ((1 + ‖x' - z‖) ^ 4)⁻¹ := hρ
        _ ≤ C * ((2 + ‖x‖) ^ 4 * ((1 + ‖z‖) ^ 4)⁻¹) := by gcongr
        _ = C' * ((1 + ‖z‖) ^ 4)⁻¹ := by ring
    have hC'0 : 0 ≤ C' := by positivity
    simp only [bound]
    by_cases hz : ‖z‖ < 1
    · rw [indicator_of_mem (mem_ball_zero_iff.mpr hz)]
      have h1 : ((1 + ‖z‖) ^ 4)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [norm_nonneg z]))
      calc |ρ (x' - z)| * (‖z‖ ^ 2)⁻¹ ≤ C' * ((1 + ‖z‖) ^ 4)⁻¹ * (‖z‖ ^ 2)⁻¹ := by gcongr
        _ ≤ C' * 1 * (‖z‖ ^ 2)⁻¹ := by gcongr
        _ ≤ C' * ((‖z‖ ^ 2)⁻¹ + ((1 + ‖z‖) ^ 4)⁻¹) := by
            rw [mul_one]; gcongr; linarith [show (0:ℝ) ≤ ((1 + ‖z‖) ^ 4)⁻¹ by positivity]
    · rw [indicator_of_notMem (fun h' => hz (mem_ball_zero_iff.mp h')), zero_add]
      have h1 : (‖z‖ ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (not_lt.mp hz))
      calc |ρ (x' - z)| * (‖z‖ ^ 2)⁻¹ ≤ C' * ((1 + ‖z‖) ^ 4)⁻¹ * 1 := by gcongr
        _ = C' * ((1 + ‖z‖) ^ 4)⁻¹ := by ring
  · exact hbi
  · refine Eventually.of_forall fun z => ?_
    exact ((ρ.continuous.comp (continuous_id.sub continuous_const)).smul continuous_const).continuousAt

lemma pG_conv (G : ℝ) (ρ : SM) (x : Space) :
    Penrose.potentialGradient G ρ x = -G • ∫ z, ρ (x - z) • K z := by
  rw [pG_eq]
  congr 1
  rw [← integral_sub_left_eq_self (fun z => ρ (x - z) • K z) volume x]
  simp only [sub_sub_cancel]

lemma pG_cont (G : ℝ) (ρ : SM) : Continuous (Penrose.potentialGradient G ρ) := by
  have : Penrose.potentialGradient G ρ = fun x => -G • ∫ z, ρ (x - z) • K z := funext (pG_conv G ρ)
  rw [this]
  exact (conv_K_cont ρ).const_smul (-G)

end PenAux


open MeasureTheory Metric Real Set Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace PenAux

set_option linter.unusedSectionVars false

theorem field_grad (G : ℝ) (ρ : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℝ)
    (x : EuclideanSpace ℝ (Fin 3)) :
    HasGradientAt (Penrose.newtonianPotential G ρ) (Penrose.potentialGradient G ρ x) x := by
  rw [hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  have hc := (pG_cont G ρ).continuousAt (x := x)
  rw [Metric.continuousAt_iff] at hc
  obtain ⟨δ, hδ, hδ'⟩ := hc ε hε
  filter_upwards [Metric.ball_mem_nhds 0 hδ] with h hh
  rw [incr, InnerProductSpace.toDual_apply_apply]
  have hint : IntervalIntegrable (fun s : ℝ => inner ℝ (Penrose.potentialGradient G ρ (x + s • h)) h)
      volume 0 1 := by
    apply Continuous.intervalIntegrable
    exact ((pG_cont G ρ).comp (continuous_const.add (continuous_id.smul continuous_const))).inner
      continuous_const
  have e : (∫ s in (0:ℝ)..1, inner ℝ (Penrose.potentialGradient G ρ (x + s • h)) h)
      - inner ℝ (Penrose.potentialGradient G ρ x) h
      = ∫ s in (0:ℝ)..1, inner ℝ (Penrose.potentialGradient G ρ (x + s • h)
          - Penrose.potentialGradient G ρ x) h := by
    simp_rw [inner_sub_left]
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const, intervalIntegral.integral_const]
    simp
  rw [e]
  have hb : ∀ s ∈ Set.uIoc (0:ℝ) 1, ‖inner ℝ (Penrose.potentialGradient G ρ (x + s • h)
      - Penrose.potentialGradient G ρ x) h‖ ≤ ε * ‖h‖ := by
    intro s hs
    rw [Set.uIoc_of_le zero_le_one] at hs
    refine (norm_inner_le_norm _ _).trans ?_
    gcongr
    have hd : dist (x + s • h) x < δ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs.1]
      rw [Metric.mem_ball, dist_zero_right] at hh
      calc s * ‖h‖ ≤ 1 * ‖h‖ := by gcongr; exact hs.2
        _ < δ := by linarith
    have := hδ' hd
    rw [dist_eq_norm] at this
    exact this.le
  have := intervalIntegral.norm_integral_le_of_norm_le_const hb
  simpa using this

lemma fderiv_pot (G : ℝ) (ρ : SM) :
    fderiv ℝ (Penrose.newtonianPotential G ρ) = fun y => innerSL ℝ (Penrose.potentialGradient G ρ y) := by
  funext y
  rw [(field_grad G ρ y).hasFDerivAt.fderiv]
  ext v; simp

end PenAux


open MeasureTheory Metric Real Set Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace PenAux

set_option linter.unusedSectionVars false

lemma sm_decay_n (ρ : SM) (n : ℕ) : ∃ C, 0 ≤ C ∧ ∀ w, ‖iteratedFDeriv ℝ n ρ w‖ ≤ C * ((1 + ‖w‖) ^ 4)⁻¹ := by
  set C := 2 ^ 4 * ((Finset.Iic ((4:ℕ), n)).sup fun m => SchwartzMap.seminorm ℝ m.1 m.2) ρ
  have hb : ∀ w, ‖iteratedFDeriv ℝ n ρ w‖ ≤ C * ((1 + ‖w‖) ^ 4)⁻¹ := by
    intro w
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (4, n)) le_rfl le_rfl ρ w
    simp only at h
    have hp : 0 < (1 + ‖w‖) ^ 4 := by positivity
    rw [le_mul_inv_iff₀ hp]
    linarith [h, mul_comm ((1 + ‖w‖) ^ 4) ‖iteratedFDeriv ℝ n ρ w‖]
  refine ⟨C, ?_, hb⟩
  have := hb 0
  have h2 : 0 < ((1 + ‖(0:Space)‖) ^ 4)⁻¹ := by positivity
  nlinarith [norm_nonneg (iteratedFDeriv ℝ n ρ 0)]

noncomputable def bnd (C : ℝ) (x z : Space) : ℝ :=
  C * (2 + ‖x‖) ^ 4 * ((ball (0:Space) 1).indicator (fun z => (‖z‖ ^ 2)⁻¹) z + ((1 + ‖z‖) ^ 4)⁻¹)

lemma bnd_integrable (C : ℝ) (x : Space) : Integrable (bnd C x) := by
  refine Integrable.const_mul ?_ _
  refine ((psi_ball_integrable 2 le_rfl).integrable_indicator measurableSet_ball).add ?_
  have := integrable_one_add_norm (E := Space) (μ := volume) (r := 4) (by simp; norm_num)
  refine this.congr (Eventually.of_forall fun z => ?_)
  simp only
  rw [rpow_neg (by positivity)]
  norm_cast

lemma dom (C : ℝ) (hC : 0 ≤ C) (x x' z : Space) (hx' : dist x' x < 1) (a : ℝ)
    (ha : a ≤ C * ((1 + ‖x' - z‖) ^ 4)⁻¹) : a * (‖z‖ ^ 2)⁻¹ ≤ bnd C x z := by
  have hd := one_add_le x x' z hx'
  set C' := C * (2 + ‖x‖) ^ 4
  have hq : ((1 + ‖x' - z‖) ^ 4)⁻¹ ≤ (2 + ‖x‖) ^ 4 * ((1 + ‖z‖) ^ 4)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    calc ((1 + ‖x' - z‖) ^ 4)⁻¹ * (1 + ‖z‖) ^ 4
        ≤ ((1 + ‖x' - z‖) ^ 4)⁻¹ * ((1 + ‖x' - z‖) * (2 + ‖x‖)) ^ 4 := by gcongr
      _ = (2 + ‖x‖) ^ 4 := by
          rw [mul_pow]; field_simp
  have ha' : a ≤ C' * ((1 + ‖z‖) ^ 4)⁻¹ := by
    calc a ≤ C * ((1 + ‖x' - z‖) ^ 4)⁻¹ := ha
      _ ≤ C * ((2 + ‖x‖) ^ 4 * ((1 + ‖z‖) ^ 4)⁻¹) := by gcongr
      _ = C' * ((1 + ‖z‖) ^ 4)⁻¹ := by ring
  have hC'0 : 0 ≤ C' := by positivity
  unfold bnd
  by_cases hz : ‖z‖ < 1
  · rw [indicator_of_mem (mem_ball_zero_iff.mpr hz)]
    have h1 : ((1 + ‖z‖) ^ 4)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [norm_nonneg z]))
    calc a * (‖z‖ ^ 2)⁻¹ ≤ C' * ((1 + ‖z‖) ^ 4)⁻¹ * (‖z‖ ^ 2)⁻¹ := by gcongr
      _ ≤ C' * 1 * (‖z‖ ^ 2)⁻¹ := by gcongr
      _ ≤ C' * ((‖z‖ ^ 2)⁻¹ + ((1 + ‖z‖) ^ 4)⁻¹) := by
          rw [mul_one]; gcongr; linarith [show (0:ℝ) ≤ ((1 + ‖z‖) ^ 4)⁻¹ by positivity]
  · rw [indicator_of_notMem (fun h' => hz (mem_ball_zero_iff.mp h')), zero_add]
    have h1 : (‖z‖ ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (not_lt.mp hz))
    rcases le_total 0 a with h0 | h0
    · calc a * (‖z‖ ^ 2)⁻¹ ≤ C' * ((1 + ‖z‖) ^ 4)⁻¹ * 1 := by gcongr
        _ = C' * ((1 + ‖z‖) ^ 4)⁻¹ := by ring
    · have : a * (‖z‖ ^ 2)⁻¹ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h0 (by positivity)
      linarith [show 0 ≤ C' * ((1 + ‖z‖) ^ 4)⁻¹ by positivity]

noncomputable def DpG (G : ℝ) (ρ : SM) (x : Space) : Space →L[ℝ] Space :=
  -G • ∫ z, (fderiv ℝ ρ (x - z)).smulRight (K z)

lemma fderiv_cont (ρ : SM) : Continuous (fderiv ℝ ρ) :=
  (ρ.smooth ⊤).continuous_fderiv (by simp)

lemma smulRight_aesm (ρ : SM) (x : Space) :
    AEStronglyMeasurable (fun z => (fderiv ℝ ρ (x - z)).smulRight (K z)) := by
  have h1 : AEStronglyMeasurable (fun z => fderiv ℝ ρ (x - z)) volume :=
    ((fderiv_cont ρ).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have h2 : AEStronglyMeasurable K volume := K_meas.aestronglyMeasurable
  have := (ContinuousLinearMap.smulRightL ℝ Space Space).continuous₂.comp_aestronglyMeasurable₂ h1 h2
  refine this.congr (Eventually.of_forall fun z => ?_)
  ext v; simp

lemma pG_hasFDerivAt (G : ℝ) (ρ : SM) (x : Space) :
    HasFDerivAt (Penrose.potentialGradient G ρ) (DpG G ρ x) x := by
  obtain ⟨C0, hC0, hd0⟩ := sm_decay_n ρ 0
  obtain ⟨C1, hC1, hd1⟩ := sm_decay_n ρ 1
  have hfun : Penrose.potentialGradient G ρ = fun x => -G • ∫ z, ρ (x - z) • K z := funext (pG_conv G ρ)
  rw [hfun]
  unfold DpG
  suffices hI : HasFDerivAt (fun x => ∫ z, ρ (x - z) • K z)
      (∫ z, (fderiv ℝ ρ (x - z)).smulRight (K z)) x from hI.const_smul (-G)
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := bnd C1 x) (ball_mem_nhds x one_pos)
  · refine Eventually.of_forall fun x' => ?_
    have := ρ.continuous.measurable
    exact ((this.comp (measurable_const.sub measurable_id)).smul K_meas).aestronglyMeasurable
  · refine (bnd_integrable C0 x).mono' ?_ (Eventually.of_forall fun z => ?_)
    · have := ρ.continuous.measurable
      exact ((this.comp (measurable_const.sub measurable_id)).smul K_meas).aestronglyMeasurable
    · rw [norm_smul, norm_K]
      apply dom C0 hC0 x x z (by simp)
      have := hd0 (x - z)
      rwa [norm_iteratedFDeriv_zero] at this
  · exact smulRight_aesm ρ x
  · refine Eventually.of_forall fun z x' hx' => ?_
    rw [ContinuousLinearMap.norm_smulRight_apply, norm_K]
    apply dom C1 hC1 x x' z (mem_ball.mp hx')
    have := hd1 (x' - z)
    rwa [norm_iteratedFDeriv_one] at this
  · exact bnd_integrable C1 x
  · refine Eventually.of_forall fun z x' _ => ?_
    have h1 : HasFDerivAt (fun y : Space => ρ (y - z)) (fderiv ℝ ρ (x' - z)) x' := by
      have := (ρ.differentiableAt (x := x' - z)).hasFDerivAt.comp x' ((hasFDerivAt_id x').sub_const z)
      simp only [ContinuousLinearMap.comp_id] at this
      exact this
    exact h1.smul_const (K z)

end PenAux


open MeasureTheory Metric Real Set Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace PenAux

set_option linter.unusedSectionVars false

noncomputable abbrev ee (i : Fin 3) : Space := EuclideanSpace.single i 1

lemma lap_eq (G : ℝ) (ρ : SM) (x : Space) :
    Penrose.laplacian (Penrose.newtonianPotential G ρ) x = ∑ i, ⟪DpG G ρ x (ee i), ee i⟫ := by
  unfold Penrose.laplacian
  congr 1; funext i
  rw [iteratedFDeriv_two_apply, fderiv_pot]
  have h : HasFDerivAt (fun y => innerSL ℝ (Penrose.potentialGradient G ρ y))
      ((innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).comp (DpG G ρ x)) x :=
    (innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).hasFDerivAt.comp x (pG_hasFDerivAt G ρ x)
  rw [h.fderiv]
  simp

lemma smulRight_integrable (ρ : SM) (x : Space) :
    Integrable (fun z => (fderiv ℝ ρ (x - z)).smulRight (K z)) := by
  obtain ⟨C1, hC1, hd1⟩ := sm_decay_n ρ 1
  refine (bnd_integrable C1 x).mono' (smulRight_aesm ρ x) (Eventually.of_forall fun z => ?_)
  rw [ContinuousLinearMap.norm_smulRight_apply, norm_K]
  apply dom C1 hC1 x x z (by simp)
  have := hd1 (x - z)
  rwa [norm_iteratedFDeriv_one] at this

lemma sum_basis (v : Space) : ∑ i, v.ofLp i • ee i = v := by
  have := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
  simpa [EuclideanSpace.basisFun_repr] using this

lemma div_eq (G : ℝ) (ρ : SM) (x : Space) :
    ∑ i, ⟪DpG G ρ x (ee i), ee i⟫ = -G * ∫ z, fderiv ℝ ρ (x - z) (K z) := by
  have hI := smulRight_integrable ρ x
  have hterm : ∀ i, ⟪DpG G ρ x (ee i), ee i⟫ =
      -G * ∫ z, fderiv ℝ ρ (x - z) (ee i) * (K z).ofLp i := by
    intro i
    unfold DpG
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.integral_apply hI, inner_smul_left,
      real_inner_comm, ← integral_inner (hI.apply_continuousLinearMap (ee i))]
    simp [EuclideanSpace.inner_single_left, mul_comm]
  simp_rw [hterm]
  rw [← Finset.mul_sum, ← integral_finset_sum]
  · congr 1
    congr 1; funext z
    conv_rhs => rw [← sum_basis (K z)]
    rw [map_sum]
    congr 1; funext i
    rw [map_smul, smul_eq_mul, mul_comm]
  · intro i _
    have h1 := hI.apply_continuousLinearMap (ee i)
    have h2 := h1.inner_const (𝕜 := ℝ) (ee i)
    refine h2.congr (Eventually.of_forall fun z => ?_)
    simp [EuclideanSpace.inner_single_right]

end PenAux


open MeasureTheory Metric Real Set Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace PenAux

set_option linter.unusedSectionVars false

lemma one_add_le' (x z : Space) : 1 + ‖z‖ ≤ (1 + ‖x - z‖) * (1 + ‖x‖) := by
  have h1 : ‖z‖ ≤ ‖x - z‖ + ‖x‖ := by
    have := norm_sub_le x (x - z)
    simp only [sub_sub_cancel] at this
    linarith [norm_sub_rev x z]
  nlinarith [norm_nonneg (x - z), norm_nonneg x]

lemma decay_ray (C : ℝ) (hC : 0 ≤ C) (x : Space) (ω : sphere (0:Space) 1) (r : ℝ) (hr : 0 ≤ r)
    (a : ℝ) (ha : a ≤ C * ((1 + ‖x - r • (ω : Space)‖) ^ 4)⁻¹) :
    a ≤ C * (1 + ‖x‖) ^ 4 * ((1 + r) ^ 4)⁻¹ := by
  have hn : ‖r • (ω : Space)‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr]; simp
  have hd := one_add_le' x (r • (ω : Space))
  rw [hn] at hd
  refine ha.trans ?_
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hC
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  calc ((1 + ‖x - r • (ω : Space)‖) ^ 4)⁻¹ * (1 + r) ^ 4
      ≤ ((1 + ‖x - r • (ω : Space)‖) ^ 4)⁻¹ * ((1 + ‖x - r • (ω : Space)‖) * (1 + ‖x‖)) ^ 4 := by
        gcongr
    _ = (1 + ‖x‖) ^ 4 := by rw [mul_pow]; field_simp

lemma integrableOn_inv_pow : IntegrableOn (fun r : ℝ => ((1 + r) ^ 4)⁻¹) (Ioi 0) := by
  have := integrable_one_add_norm (E := ℝ) (μ := volume) (r := 4) (by norm_num)
  refine (this.integrableOn (s := Ioi 0)).congr_fun (fun r hr => ?_) measurableSet_Ioi
  have hr' : 0 < r := hr
  simp only [Real.norm_eq_abs, abs_of_pos hr']
  rw [rpow_neg (by positivity)]
  norm_cast

lemma ray_integral (ρ : SM) (x : Space) (ω : sphere (0:Space) 1) :
    ∫ r in Ioi (0:ℝ), fderiv ℝ ρ (x - r • (ω : Space)) (ω : Space) = ρ x := by
  obtain ⟨C0, hC0, hd0⟩ := sm_decay_n ρ 0
  obtain ⟨C1, hC1, hd1⟩ := sm_decay_n ρ 1
  have hderiv : ∀ r : ℝ, HasDerivAt (fun r : ℝ => -ρ (x - r • (ω : Space)))
      (fderiv ℝ ρ (x - r • (ω : Space)) (ω : Space)) r := by
    intro r
    have h1 : HasDerivAt (fun r : ℝ => x - r • (ω : Space)) (-((1:ℝ) • (ω : Space))) r :=
      ((hasDerivAt_id r).smul_const (ω : Space)).const_sub x
    have h2 := (ρ.differentiableAt (x := x - r • (ω : Space))).hasFDerivAt.comp_hasDerivAt r h1
    have h3 := h2.neg
    simp only [one_smul, map_neg, neg_neg] at h3
    exact h3
  have hcont : Continuous (fun r : ℝ => -ρ (x - r • (ω : Space))) := by
    have := ρ.continuous; fun_prop
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (m := 0) hcont.continuousWithinAt
    (fun r _ => hderiv r)]
  · simp
  · refine (integrableOn_inv_pow.const_mul (C1 * (1 + ‖x‖) ^ 4)).mono' ?_ ?_
    · have := fderiv_cont ρ
      exact (by fun_prop : Continuous fun r : ℝ => fderiv ℝ ρ (x - r • (ω : Space)) (ω : Space)).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      have hr' : 0 ≤ r := le_of_lt hr
      apply decay_ray C1 hC1 x ω r hr'
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      have hw : ‖(ω : Space)‖ = 1 := by simp
      rw [hw, mul_one]
      have := hd1 (x - r • (ω : Space))
      rwa [norm_iteratedFDeriv_one] at this
  · have hlim : Tendsto (fun r : ℝ => C0 * (1 + ‖x‖) ^ 4 * ((1 + r) ^ 4)⁻¹) atTop (𝓝 0) := by
      have : Tendsto (fun r : ℝ => ((1 + r) ^ 4)⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by norm_num)).comp
          (tendsto_atTop_add_const_left _ 1 tendsto_id))
      simpa using this.const_mul (C0 * (1 + ‖x‖) ^ 4)
    rw [show (0:ℝ) = -0 by simp]
    apply Tendsto.neg
    apply squeeze_zero_norm' _ hlim
    filter_upwards [eventually_ge_atTop 0] with r hr
    apply decay_ray C0 hC0 x ω r hr
    have := hd0 (x - r • (ω : Space))
    rwa [norm_iteratedFDeriv_zero] at this

lemma radial (ρ : SM) (x : Space) : ∫ z, fderiv ℝ ρ (x - z) (K z) = 4 * π * ρ x := by
  obtain ⟨C1, hC1, hd1⟩ := sm_decay_n ρ 1
  have hf : Integrable (fun z => fderiv ℝ ρ (x - z) (K z)) := by
    refine (bnd_integrable C1 x).mono' ?_ (Eventually.of_forall fun z => ?_)
    · have h1 : AEStronglyMeasurable (fun z => fderiv ℝ ρ (x - z)) volume :=
        ((fderiv_cont ρ).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      exact (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := Space) (F := ℝ)).continuous.comp_aestronglyMeasurable₂
        h1 K_meas.aestronglyMeasurable
    · refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      rw [norm_K]
      apply dom C1 hC1 x x z (by simp)
      have := hd1 (x - z)
      rwa [norm_iteratedFDeriv_one] at this
  rw [polar_integral, integral_prod _ (polar_integrable _ hf)]
  have hin : ∀ ω : sphere (0:Space) 1,
      ∫ r, fderiv ℝ ρ (x - r.1 • (ω : Space)) (K (r.1 • (ω : Space))) ∂nu = ρ x := by
    intro ω
    rw [nu_integral (fun r => fderiv ℝ ρ (x - r • (ω : Space)) (K (r • (ω : Space))))]
    rw [setIntegral_congr_fun measurableSet_Ioi (g := fun r => fderiv ℝ ρ (x - r • (ω : Space)) (ω : Space))
      (fun r hr => by
        have hr' : 0 < r := hr
        simp only
        rw [K_smul r hr' ω, map_smul, smul_smul, smul_eq_mul]
        field_simp)]
    exact ray_integral ρ x ω
  simp_rw [hin]
  rw [integral_const, sig_real_univ, smul_eq_mul]

end PenAux


open MeasureTheory Metric Real Set Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace PenAux

set_option linter.unusedSectionVars false

theorem poisson (G : ℝ) (ρ : SM) (x : Space) :
    Penrose.laplacian (Penrose.newtonianPotential G ρ) x = -(4 * Real.pi) * G * ⇑ρ x := by
  rw [lap_eq, div_eq, radial]; ring

theorem pairing (G : ℝ) (ρ ρ' : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℝ) :
    Penrose.deltaMeasure G ρ ρ'
      = 4 * Real.pi * G * ∫ x, (Penrose.newtonianPotential G ρ x - Penrose.newtonianPotential G ρ' x)
            * (⇑ρ x - ⇑ρ' x) ∂volume := by
  rw [core]
  have h : ∀ x, (Penrose.newtonianPotential G ρ x - Penrose.newtonianPotential G ρ' x)
      * (ρ x - ρ' x) = G * ∫ y, (ρ x - ρ' x) * (ρ y - ρ' y) / ‖x - y‖ := by
    intro x
    rw [pot_sub, mul_assoc, mul_comm (∫ y, _ ∂volume), ← integral_const_mul]
    congr 2; funext y; ring
  simp_rw [h]
  rw [integral_const_mul]
  ring

lemma pot_sub_fun (G : ℝ) (ρ ρ' : SM) :
    (fun y => Penrose.newtonianPotential G ρ y - Penrose.newtonianPotential G ρ' y) =
      Penrose.newtonianPotential G (ρ - ρ') := by
  funext y
  rw [pot_sub]
  unfold Penrose.newtonianPotential
  simp

end PenAux

open MeasureTheory in
theorem solution (G : ℝ) (ρ ρ' : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℝ) :
    Penrose.deltaMeasure G ρ ρ'
      = -∫ x, (Penrose.newtonianPotential G ρ x - Penrose.newtonianPotential G ρ' x)
            * Penrose.laplacian (fun y => Penrose.newtonianPotential G ρ y - Penrose.newtonianPotential G ρ' y) x
          ∂volume := by
  rw [PenAux.pot_sub_fun, PenAux.pairing]
  simp_rw [PenAux.poisson, SchwartzMap.sub_apply]
  rw [← integral_neg]
  rw [← integral_const_mul]
  congr 1; funext x
  ring

