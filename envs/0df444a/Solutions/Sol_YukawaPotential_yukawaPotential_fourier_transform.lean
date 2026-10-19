-- Prove2me | solution 1 for YukawaPotential.yukawaPotential_fourier_transform
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T12:09:17.35749+00:00
-- url     : https://prove2.me/submissions/9e3acef7-43b8-4103-99d3-db3c3be23ad6

import Mathlib
import Definitions.Def_NewtonGravitation_Defs
import Definitions.Def_YukawaPotential_Defs


open MeasureTheory NewtonGravitation Metric
open scoped Pointwise

namespace NGAux

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

lemma shell_phi_meas (a : ℝ) :
    Measurable (fun u : sphere (0 : Space) 1 => a • (u : Space)) :=
  (continuous_subtype_val.const_smul a).measurable

lemma toSphere_univ_ne_zero : (volume : Measure Space).toSphere Set.univ ≠ 0 := by
  rw [Ne, Measure.measure_univ_eq_zero]; exact Measure.toSphere_ne_zero _

lemma shell_const_ne_top (M : NNReal) :
    ((M : ENNReal) / (volume : Measure Space).toSphere Set.univ) ≠ ⊤ :=
  ENNReal.div_ne_top ENNReal.coe_ne_top toSphere_univ_ne_zero

lemma uniformShell_isFinite (M : NNReal) (a : ℝ) : IsFiniteMeasure (uniformShell M a) := by
  constructor
  rw [uniformShell, Measure.smul_apply, Measure.map_apply (shell_phi_meas a) MeasurableSet.univ,
    smul_eq_mul]
  exact ENNReal.mul_lt_top (shell_const_ne_top M).lt_top (measure_lt_top _ _)

lemma uniformShell_symm (M : NNReal) (a : ℝ) : IsSphericallySymmetric (uniformShell M a) := by
  intro A
  rw [uniformShell, Measure.map_smul, Measure.map_map A.continuous.measurable (shell_phi_meas a)]
  have : (A ∘ fun u : sphere (0 : Space) 1 => a • (u : Space)) =
      (fun u : sphere (0 : Space) 1 => a • (u : Space)) ∘ sph A := by
    funext u; simp [sph]
  rw [this, ← Measure.map_map (shell_phi_meas a) (sph_measurable A), toSphere_map_sph]

lemma uniformShell_ball (M : NNReal) (a : ℝ) (ha : 0 < a) :
    (uniformShell M a) (Metric.ball (0 : Space) a) = 0 := by
  rw [uniformShell, Measure.smul_apply, Measure.map_apply (shell_phi_meas a) measurableSet_ball]
  have : (fun u : sphere (0 : Space) 1 => a • (u : Space)) ⁻¹' Metric.ball 0 a = ∅ := by
    ext u; simp [norm_smul, abs_of_pos ha]
  simp [this]

end NGAux


open MeasureTheory NewtonGravitation Metric
open scoped Pointwise

namespace NGAux

lemma G_pos : 0 < G := by unfold G; norm_num

lemma finrank_space : Module.finrank ℝ Space = 3 := finrank_euclideanSpace_fin

lemma kern_meas : Measurable (fun z : Space => -(G / ‖z‖ ^ 3) • z) := by fun_prop

lemma kern_integrableOn_ball (ρ : ℝ) :
    IntegrableOn (fun z : Space => -(G / ‖z‖ ^ 3) • z) (ball 0 ρ) volume := by
  refine integrableOn_ball_of_norm_le_rpow (α := 2) (C := G) (by rw [finrank_space]; norm_num)
    (by rw [finrank_space]; norm_num) (Filter.Eventually.of_forall fun z => ?_)
    kern_meas.aestronglyMeasurable
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos (div_pos G_pos (pow_pos hn 3)),
    Real.rpow_neg hn.le, Real.rpow_two]
  field_simp
  rfl

lemma kern_integrableOn_shift (x : Space) (R : ℝ) :
    IntegrableOn (fun y : Space => -(G / ‖x - y‖ ^ 3) • (x - y)) (ball 0 R) volume := by
  have h1 := (kern_integrableOn_ball (‖x‖ + R)).integrable_indicator measurableSet_ball
  have h2 := h1.comp_sub_left x
  refine (h2.integrableOn (s := ball 0 R)).congr_fun (fun y hy => ?_) measurableSet_ball
  have : x - y ∈ ball (0 : Space) (‖x‖ + R) := by
    rw [mem_ball_zero_iff] at hy ⊢
    calc ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
      _ < _ := by linarith
  simp [Set.indicator_of_mem this]

lemma vol_ball_ne_zero (R : ℝ) (hR : 0 < R) : volume (ball (0 : Space) R) ≠ 0 :=
  (measure_ball_pos volume 0 hR).ne'

lemma ball_const_ne_top (M : NNReal) (R : ℝ) (hR : 0 < R) :
    ((M : ENNReal) / volume (ball (0 : Space) R)) ≠ ⊤ :=
  ENNReal.div_ne_top ENNReal.coe_ne_top (vol_ball_ne_zero R hR)

lemma uniformBall_isFinite (M : NNReal) (R : ℝ) (hR : 0 < R) :
    IsFiniteMeasure (uniformBall M R) := by
  constructor
  rw [uniformBall, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, smul_eq_mul]
  exact ENNReal.mul_lt_top (ball_const_ne_top M R hR).lt_top
    (measure_lt_top_of_subset Set.inter_subset_right measure_ball_lt_top.ne)

lemma uniformBall_symm (M : NNReal) (R : ℝ) : IsSphericallySymmetric (uniformBall M R) := by
  intro A
  rw [uniformBall, Measure.map_smul]
  congr 1
  have hpre : A ⁻¹' ball (0 : Space) R = ball 0 R := by ext y; simp
  have hA : MeasurePreserving A volume volume := A.measurePreserving
  conv_lhs => rw [← hpre]
  rw [← Measure.restrict_map A.continuous.measurable measurableSet_ball, hA.map_eq]

lemma uniformBall_real_ball (M : NNReal) (R : ℝ) (hR : 0 < R) (r : ℝ) (hr : 0 ≤ r) :
    (uniformBall M R).real (ball (0 : Space) r) = (M : ℝ) * (min r R / R) ^ 3 := by
  rw [uniformBall, measureReal_def, Measure.smul_apply, Measure.restrict_apply measurableSet_ball,
    smul_eq_mul]
  have hb : ball (0 : Space) r ∩ ball 0 R = ball 0 (min r R) := by
    ext y; simp
  rw [hb, Measure.addHaar_ball _ _ (le_min hr hR.le), Measure.addHaar_ball _ _ hR.le,
    finrank_space]
  have h1 : volume (ball (0 : Space) 1) ≠ 0 := vol_ball_ne_zero 1 one_pos
  have h2 : volume (ball (0 : Space) 1) ≠ ⊤ := measure_ball_lt_top.ne
  rw [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]
  have h3 : (volume (ball (0 : Space) 1)).toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨h1, h2⟩
  simp only [ENNReal.coe_toReal]
  field_simp

end NGAux

open MeasureTheory NewtonGravitation Metric Real
open scoped Pointwise ENNReal

namespace NGAux

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

end NGAux

open MeasureTheory NewtonGravitation Metric Real
open scoped Pointwise ENNReal RealInnerProductSpace

namespace NGAux

noncomputable def kern (z : Space) : Space := -(G / ‖z‖ ^ 3) • z

lemma kern_meas' : Measurable kern := kern_meas

lemma kern_isom (A : Space ≃ₗᵢ[ℝ] Space) (z : Space) : kern (A z) = A (kern z) := by
  simp [kern, map_smul]

lemma norm_kern (z : Space) : ‖kern z‖ = G / ‖z‖ ^ 2 := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp [kern]
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  rw [kern, norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos (div_pos G_pos (pow_pos hn 3))]
  field_simp

noncomputable def e0 : Space := EuclideanSpace.single 0 1

lemma norm_e0 : ‖e0‖ = 1 := by simp [e0]

lemma exists_isom (v : Space) (hv : ‖v‖ = 1) : ∃ A : Space ≃ₗᵢ[ℝ] Space, A e0 = v :=
  ⟨Submodule.reflection (ℝ ∙ (e0 - v))ᗮ, Submodule.reflection_sub (by rw [norm_e0, hv])⟩

variable {μ : Measure Space}

lemma mp_of_symm (hμ : IsSphericallySymmetric μ) (A : Space ≃ₗᵢ[ℝ] Space) :
    MeasurePreserving A μ μ := ⟨A.continuous.measurable, hμ A⟩

lemma integrable_isom (hμ : IsSphericallySymmetric μ) (x : Space)
    (hint : Integrable (fun y => kern (x - y)) μ) (A : Space ≃ₗᵢ[ℝ] Space) :
    Integrable (fun y => kern (A x - y)) μ := by
  rw [← (mp_of_symm hμ A).integrable_comp_emb A.toHomeomorph.measurableEmbedding]
  have : ((fun y => kern (A x - y)) ∘ A) = fun y => A (kern (x - y)) := by
    funext y; simp [← map_sub, kern_isom]
  rw [this]
  exact (A.toContinuousLinearEquiv : Space →L[ℝ] Space).integrable_comp hint

lemma integral_isom (hμ : IsSphericallySymmetric μ) (x : Space) (A : Space ≃ₗᵢ[ℝ] Space)
    (f : Space → Space → ℝ) (hf : ∀ y, f (A x) (A y) = f x y) :
    ∫ y, f (A x) y ∂μ = ∫ y, f x y ∂μ := by
  rw [← (mp_of_symm hμ A).integral_comp A.toHomeomorph.measurableEmbedding]
  simp [hf]

lemma gravField_isom (hμ : IsSphericallySymmetric μ) (x : Space) (A : Space ≃ₗᵢ[ℝ] Space) :
    gravField μ (A x) = A (gravField μ x) := by
  unfold gravField
  rw [← (mp_of_symm hμ A).integral_comp A.toHomeomorph.measurableEmbedding]
  have : ∀ y, -(G / ‖A x - A y‖ ^ 3) • (A x - A y) = A (kern (x - y)) := by
    intro y
    show kern (A x - A y) = _
    rw [← map_sub, kern_isom]
  simp_rw [this]
  exact A.toLinearIsometry.integral_comp_comm _

lemma grav_parallel (hμ : IsSphericallySymmetric μ) (x : Space) :
    gravField μ x = (⟪gravField μ x, x⟫ / ‖x‖ ^ 2) • x := by
  set g := gravField μ x with hg
  set c := ⟪g, x⟫ / ‖x‖ ^ 2
  set w := g - c • x with hw
  rcases eq_or_ne x 0 with rfl | hx
  · -- g = gravField μ 0 = -g by the reflection `-id`
    have h := gravField_isom hμ 0 (LinearIsometryEquiv.neg ℝ)
    simp only [LinearIsometryEquiv.coe_neg, Pi.neg_apply, neg_zero] at h
    rw [← hg] at h
    have : g = 0 := by
      have h2 : (2:ℝ) • g = 0 := by rw [two_smul]; nth_rewrite 1 [h]; simp
      exact (smul_eq_zero.mp h2).resolve_left two_ne_zero
    simp [this]
  have hxn : ‖x‖ ^ 2 ≠ 0 := by positivity
  have hxw : ⟪w, x⟫ = 0 := by
    rw [hw, inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq]
    simp only [conj_trivial, c]; field_simp; ring
  set R := Submodule.reflection (ℝ ∙ w)ᗮ
  have hRx : R x = x := Submodule.reflection_mem_subspace_eq_self
    ((Submodule.mem_orthogonal_singleton_iff_inner_right).mpr hxw)
  have hRg : R g = g := by rw [hg, ← gravField_isom hμ x R, hRx]
  have hRw : R w = -w := Submodule.reflection_orthogonalComplement_singleton_eq_neg w
  have hgw : ⟪g, w⟫ = 0 := by
    have := R.inner_map_map g w
    rw [hRg, hRw, inner_neg_right] at this
    linarith
  have hww : ⟪w, w⟫ = 0 := by
    have : ⟪w, w⟫ = ⟪g, w⟫ - c * ⟪x, w⟫ := by
      conv_lhs => rw [hw]
      rw [inner_sub_left, inner_smul_left]; simp [hw]
    rw [this, hgw, real_inner_comm, hxw]; ring
  have : w = 0 := inner_self_eq_zero.mp hww
  rw [hw, sub_eq_zero] at this
  exact this

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

lemma inner_kern_e0 (r s : ℝ) (u : sphere (0 : Space) 1) :
    ⟪kern (r • (u : Space) - s • e0), (u : Space)⟫ = -G * f0 r s (c0 u) := by
  have hu : ‖(u : Space)‖ = 1 := by simp
  have huu : ⟪(u : Space), (u : Space)⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
  have hn : ‖r • (u : Space) - s • e0‖ = √(r ^ 2 - 2 * r * s * c0 u + s ^ 2) := by
    rw [← sqrt_sq (norm_nonneg _), norm_sub_sq_real, norm_smul, norm_smul, inner_smul_left,
      inner_smul_right, hu, norm_e0, real_inner_comm, inner_e0]
    simp only [Real.norm_eq_abs, conj_trivial, c0]
    congr 1; rw [mul_pow, mul_pow, sq_abs, sq_abs]; ring
  rw [kern, inner_smul_left, hn, inner_sub_left, inner_smul_left, inner_smul_left, huu, inner_e0]
  simp only [conj_trivial, f0, c0]
  ring

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

lemma shell_y (r : ℝ) (hr : 0 < r) (y : Space) (hy : ‖y‖ ≠ r) :
    ∫ u, ⟪kern (r • (u : Space) - y), (u : Space)⟫ ∂sig = if ‖y‖ < r then -(4 * π * G / r ^ 2) else 0 := by
  rw [rotate_to_e0 r y (fun z u => ⟪kern z, u⟫) (fun A z u => by simp [kern_isom])]
  simp_rw [inner_kern_e0]
  rw [integral_const_mul, arch_integral _ (f0_meas r ‖y‖), shell_ftc r ‖y‖ hr (norm_nonneg y) hy]
  split_ifs
  · field_simp; ring
  · simp

lemma norm_sub_e0_sq (r s : ℝ) (u : sphere (0 : Space) 1) :
    ‖r • (u : Space) - s • e0‖ ^ 2 = r ^ 2 - 2 * r * s * c0 u + s ^ 2 := by
  have hu : ‖(u : Space)‖ = 1 := by simp
  rw [norm_sub_sq_real, norm_smul, norm_smul, inner_smul_left,
    inner_smul_right, hu, norm_e0, real_inner_comm, inner_e0]
  simp only [Real.norm_eq_abs, conj_trivial, c0]
  rw [mul_pow, mul_pow, sq_abs, sq_abs]; ring

lemma not_integrable_singular (r : ℝ) (hr : 0 < r) (y : Space) (hy : ‖y‖ = r) :
    ¬ Integrable (fun u : sphere (0 : Space) 1 => kern (r • (u : Space) - y)) sig := by
  intro h
  obtain ⟨A, hA⟩ := exists_isom_of y
  rw [hy] at hA
  rw [← sig_integrable_isom A] at h
  have h1 : ∀ u : sphere (0 : Space) 1, kern (r • ((sph A u : sphere (0 : Space) 1) : Space) - y) =
      A (kern (r • (u : Space) - r • e0)) := by
    intro u
    rw [← kern_isom]; congr 1
    conv_lhs => rw [hA]
    simp [sph, map_sub, map_smul]
  simp_rw [h1] at h
  have h2 := h.norm
  simp_rw [LinearIsometryEquiv.norm_map, norm_kern, norm_sub_e0_sq] at h2
  set hfun : ℝ → ℝ := fun t => G / (r ^ 2 - 2 * r * r * t + r ^ 2) with hhf
  have h3 := arch_integrable hfun (by rw [hhf]; fun_prop) h2
  have h4 : IntervalIntegrable hfun volume (-1) 1 :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).mpr h3
  have h5 : IntervalIntegrable (fun t : ℝ => (t - 1)⁻¹) volume (-1) 1 := by
    have := h4.const_mul (-(2 * r ^ 2) / G)
    refine this.congr ?_
    intro t _
    simp only [hhf]
    have hG := G_pos
    rcases eq_or_ne t 1 with rfl | ht
    · simp; right; right; ring
    · have : t - 1 ≠ 0 := sub_ne_zero.mpr ht
      have : r ^ 2 - 2 * r * r * t + r ^ 2 = -(2 * r ^ 2) * (t - 1) := by ring
      rw [this]
      field_simp
  rw [intervalIntegrable_sub_inv_iff] at h5
  rcases h5 with h5 | h5
  · norm_num at h5
  · exact h5 (by rw [Set.uIcc_of_le (by norm_num)]; constructor <;> norm_num)

lemma exists_isom_xu (x : Space) (hx : x ≠ 0) (u : sphere (0 : Space) 1) :
    ∃ A : Space ≃ₗᵢ[ℝ] Space, A x = ‖x‖ • (u : Space) ∧ A (‖x‖⁻¹ • x) = u := by
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  obtain ⟨B, hB⟩ := exists_isom (‖x‖⁻¹ • x) (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne'])
  obtain ⟨C, hC⟩ := exists_isom (u : Space) (by simp)
  refine ⟨B.symm.trans C, ?_, ?_⟩
  · have : x = ‖x‖ • B e0 := by rw [hB, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    conv_lhs => rw [this]
    simp [hC]
  · have : ‖x‖⁻¹ • x = B e0 := hB.symm
    rw [this]; simp [hC]

theorem radial_kernel (μ : Measure Space) [IsFiniteMeasure μ]
    (hμ : IsSphericallySymmetric μ) (x : Space)
    (hint : Integrable (fun y => -(G / ‖x - y‖ ^ 3) • (x - y)) μ) :
    gravField μ x =
      ∫ r : ℝ, (if r < ‖x‖ then (-(G / ‖x‖ ^ 3)) • x else 0)
        ∂(μ.map (fun y : Space => ‖y‖)) := by
  have hint' : Integrable (fun y => kern (x - y)) μ := hint
  -- right-hand side
  have hR : ∫ r : ℝ, (if r < ‖x‖ then (-(G / ‖x‖ ^ 3)) • x else 0) ∂(μ.map (fun y : Space => ‖y‖)) =
      μ.real (ball 0 ‖x‖) • ((-(G / ‖x‖ ^ 3)) • x) := by
    rw [integral_map (by fun_prop)]
    · have : (fun y : Space => if ‖y‖ < ‖x‖ then (-(G / ‖x‖ ^ 3)) • x else 0) =
          (ball (0 : Space) ‖x‖).indicator (fun _ => (-(G / ‖x‖ ^ 3)) • x) := by
        funext y; simp [Set.indicator, mem_ball_zero_iff]
      rw [this, integral_indicator_const _ measurableSet_ball]
    · exact (Measurable.ite measurableSet_Iio measurable_const measurable_const).aestronglyMeasurable
  rw [hR, grav_parallel hμ x]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  set r := ‖x‖ with hrdef
  set g := gravField μ x with hg
  -- the joint function
  set Φ : sphere (0 : Space) 1 × Space → Space := fun p => kern (r • (p.1 : Space) - p.2) with hΦ
  have hΦm : Measurable Φ := kern_meas'.comp (by fun_prop)
  have hfib : ∀ u : sphere (0 : Space) 1, Integrable (fun y => kern (r • (u : Space) - y)) μ := by
    intro u
    obtain ⟨A, hA1, -⟩ := exists_isom_xu x hx u
    have := integrable_isom hμ x hint' A
    rwa [hA1] at this
  have hfibn : ∀ u : sphere (0 : Space) 1, ∫ y, ‖kern (r • (u : Space) - y)‖ ∂μ = ∫ y, ‖kern (x - y)‖ ∂μ := by
    intro u
    obtain ⟨A, hA1, -⟩ := exists_isom_xu x hx u
    have := integral_isom hμ x A (fun x y => ‖kern (x - y)‖)
      (fun y => by rw [← map_sub, kern_isom, LinearIsometryEquiv.norm_map])
    try simp only at this
    rwa [hA1] at this
  have hΦi : Integrable Φ (sig.prod μ) := by
    rw [integrable_prod_iff hΦm.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall hfib, ?_⟩
    simp only [hΦ]
    simp_rw [hfibn]
    exact integrable_const _
  -- a.e. the source is off the sphere of radius r
  have hae : ∀ᵐ y ∂μ, ‖y‖ ≠ r := by
    filter_upwards [hΦi.prod_left_ae] with y hy
    intro hyr
    exact not_integrable_singular r hr y hyr hy
  -- inner products
  set ψ : sphere (0 : Space) 1 × Space → ℝ := fun p => ⟪Φ p, (p.1 : Space)⟫ with hψ
  have hψi : Integrable ψ (sig.prod μ) := by
    refine hΦi.mono (by
      have : Measurable ψ := by
        simp only [hψ]
        exact Measurable.inner hΦm (by fun_prop)
      exact this.aestronglyMeasurable) ?_
    filter_upwards with p
    simp only [hψ, Real.norm_eq_abs]
    calc |⟪Φ p, (p.1 : Space)⟫| ≤ ‖Φ p‖ * ‖(p.1 : Space)‖ := abs_real_inner_le_norm _ _
      _ = ‖Φ p‖ := by simp
  have hswap := integral_integral_swap (f := fun u y => ψ (u, y)) hψi
  -- left side: the integrand is the constant ⟪g, x⟫ / r
  have hL : ∀ u : sphere (0 : Space) 1, ∫ y, ψ (u, y) ∂μ = ⟪g, x⟫ / r := by
    intro u
    obtain ⟨A, hA1, hA2⟩ := exists_isom_xu x hx u
    simp only [hψ, hΦ]
    rw [show (fun y => ⟪kern (r • (u : Space) - y), (u : Space)⟫) =
        fun y => ⟪(u : Space), kern (r • (u : Space) - y)⟫ from funext fun y => real_inner_comm _ _,
      integral_inner (hfib u), real_inner_comm]
    have : ∫ y, kern (r • (u : Space) - y) ∂μ = gravField μ (A x) := by rw [hA1]; rfl
    rw [this, gravField_isom hμ x A, ← hA2, LinearIsometryEquiv.inner_map_map, ← hg,
      inner_smul_right]
    field_simp
    rw [hrdef]; ring
  -- right side
  have hRi : ∀ᵐ y ∂μ, ∫ u, ψ (u, y) ∂sig = (ball (0 : Space) r).indicator (fun _ => -(4 * π * G / r ^ 2)) y := by
    filter_upwards [hae] with y hy
    simp only [hψ, hΦ]
    rw [shell_y r hr y hy]
    by_cases h : ‖y‖ < r
    · rw [if_pos h, Set.indicator_of_mem (mem_ball_zero_iff.mpr h)]
    · rw [if_neg h, Set.indicator_of_notMem (fun h' => h (mem_ball_zero_iff.mp h'))]
  simp_rw [hL] at hswap
  rw [integral_const, integral_congr_ae hRi, integral_indicator_const _ measurableSet_ball,
    sig_real_univ, smul_eq_mul, smul_eq_mul] at hswap
  -- conclude
  have hgx : ⟪g, x⟫ = -(G * μ.real (ball 0 r) / r) := by
    have hpi : 0 < π := pi_pos
    field_simp at hswap
    have : ⟪g, x⟫ * (4 * π) = r * (μ.real (ball 0 r) * -(4 * π * G / r ^ 2)) := by
      field_simp; linarith [hswap]
    field_simp
    nlinarith [this]
  rw [hgx, smul_smul]
  congr 1
  field_simp

end NGAux


open MeasureTheory Metric Real NewtonGravitation Set
open scoped ENNReal RealInnerProductSpace

namespace YKFT
open NGAux

/-- polar coordinates in `ℝ³` -/
lemma polar (F : Space → ℂ) (hF : Integrable F) :
    ∫ x, F x = ∫ r in Ioi (0:ℝ), (r ^ 2 : ℝ) • ∫ u, F (r • (u : Space)) ∂sig := by
  have hmp := (volume : Measure Space).measurePreserving_homeomorphUnitSphereProd
  have hdim : Module.finrank ℝ Space - 1 = 2 := by simp
  rw [hdim] at hmp
  set g : sphere (0 : Space) 1 × Ioi (0:ℝ) → ℂ := fun p => F ((p.2 : ℝ) • (p.1 : Space)) with hg
  have hcomp : ∀ x : ({0}ᶜ : Set Space), g (homeomorphUnitSphereProd Space x) = F x := by
    intro x
    have hx : (x : Space) ≠ 0 := x.2
    simp [hg, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hx)]
  have h1 : ∫ x, F x = ∫ x : ({0}ᶜ : Set Space), F x ∂(volume.comap Subtype.val) := by
    rw [integral_subtype_comap (measurableSet_singleton 0).compl, restrict_compl_singleton]
  have h2 : ∫ x : ({0}ᶜ : Set Space), F x ∂(volume.comap Subtype.val) =
      ∫ p, g p ∂(sig.prod (Measure.volumeIoiPow 2)) := by
    rw [← hmp.integral_comp (Homeomorph.measurableEmbedding _)]
    simp only [hcomp]
  have hgi : Integrable g (sig.prod (Measure.volumeIoiPow 2)) := by
    rw [← hmp.integrable_comp_emb (Homeomorph.measurableEmbedding _)]
    have : Integrable (fun x : ({0}ᶜ : Set Space) => F x) (volume.comap Subtype.val) := by
      exact (integrableOn_iff_comap_subtypeVal (measurableSet_singleton 0).compl).1 hF.integrableOn
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Function.comp_apply, hcomp]
  rw [h1, h2, integral_prod_symm _ hgi, Measure.volumeIoiPow,
    integral_withDensity_eq_integral_toReal_smul (by fun_prop) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [← integral_subtype_comap measurableSet_Ioi (fun r => (r ^ 2 : ℝ) • ∫ u, F (r • (u : Space)) ∂sig)]
  congr 1; funext r
  rw [ENNReal.toReal_ofReal (by have := r.2; positivity)]

lemma arch_c (f : ℝ → ℂ) (hf : Measurable f) :
    ∫ u, f (c0 u) ∂sig = (2 * π : ℝ) • ∫ t in Ioo (-1:ℝ) 1, f t := by
  rw [← integral_map c0_meas.aemeasurable hf.aestronglyMeasurable, archimedes,
    integral_smul_measure, ENNReal.toReal_ofReal (by positivity)]

lemma interval_exp {c : ℂ} (hc : c ≠ 0) :
    ∫ t in Ioo (-1:ℝ) 1, Complex.exp (c * t) = (Complex.exp c - Complex.exp (-c)) / c := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num),
    integral_exp_mul_complex hc]
  push_cast; ring_nf

/-- the plane wave averaged over a sphere of radius `r` -/
lemma sphere_wave (k : Space) (r : ℝ) :
    ∫ u, Complex.exp (-(Complex.I * ((⟪k, r • (u : Space)⟫ : ℝ) : ℂ))) ∂sig =
      (2 * π : ℝ) • ∫ t in Ioo (-1:ℝ) 1, Complex.exp ((-(Complex.I * (r * ‖k‖ : ℝ))) * t) := by
  obtain ⟨A, hA⟩ := exists_isom_of k
  rw [← sig_integral_isom A]
  have : ∀ u : sphere (0 : Space) 1, ⟪k, r • ((sph A u : sphere (0 : Space) 1) : Space)⟫ =
      r * ‖k‖ * c0 u := by
    intro u
    conv_lhs => rw [hA]
    simp only [sph, inner_smul_left, inner_smul_right, LinearIsometryEquiv.inner_map_map, inner_e0,
      c0, conj_trivial]
    ring
  simp_rw [this]
  rw [← arch_c (fun t => Complex.exp ((-(Complex.I * (r * ‖k‖ : ℝ))) * t)) (by fun_prop)]
  congr 1; funext u
  push_cast; ring_nf

lemma V_integrable (g α m : ℝ) (ha : 0 < α * m) :
    Integrable (fun x : Space => YukawaPotential.yukawaPotential g α m ‖x‖) := by
  rw [integrable_fun_norm_addHaar volume (f := fun y => YukawaPotential.yukawaPotential g α m y)]
  have hd : Module.finrank ℝ Space - 1 = 2 := by simp
  rw [hd]
  have h := (integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := α * m) (by norm_num)
    (by norm_num) ha).const_mul (-g ^ 2)
  refine IntegrableOn.congr_fun h (fun y hy => ?_) measurableSet_Ioi
  have hy' : (0:ℝ) < y := hy
  simp only [Real.rpow_one, YukawaPotential.yukawaPotential, smul_eq_mul]
  field_simp

lemma F_integrable (g α m : ℝ) (ha : 0 < α * m) (k : Space) :
    Integrable (fun x : Space => Complex.exp (-(Complex.I * (⟪k, x⟫ : ℝ))) *
      ((YukawaPotential.yukawaPotential g α m ‖x‖ : ℝ) : ℂ)) := by
  refine (V_integrable g α m ha).norm.mono' (by
    unfold YukawaPotential.yukawaPotential; fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  have : ‖Complex.exp (-(Complex.I * (⟪k, x⟫ : ℝ)))‖ = 1 := by
    rw [show -(Complex.I * (⟪k, x⟫ : ℝ)) = ((-⟪k, x⟫ : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  rw [this, one_mul, Complex.norm_real]

theorem ft (g α m : ℝ) (hα : 0 < α) (hm : 0 < m) (k : Space) :
    ∫ x : Space, Complex.exp (-(Complex.I * (⟪k, x⟫ : ℝ))) *
        ((YukawaPotential.yukawaPotential g α m ‖x‖ : ℝ) : ℂ) =
      ((-g ^ 2 * (4 * Real.pi / (‖k‖ ^ 2 + (α * m) ^ 2)) : ℝ) : ℂ) := by
  have ha : 0 < α * m := mul_pos hα hm
  set a := α * m with ha_def
  rw [polar _ (F_integrable g α m ha k)]
  have hin : ∀ r ∈ Ioi (0:ℝ), (r ^ 2 : ℝ) • ∫ u, Complex.exp (-(Complex.I * (⟪k, r • (u : Space)⟫ : ℝ))) *
      ((YukawaPotential.yukawaPotential g α m ‖r • (u : Space)‖ : ℝ) : ℂ) ∂sig =
      (r ^ 2 : ℝ) • (((2 * π : ℝ) • ∫ t in Ioo (-1:ℝ) 1,
        Complex.exp ((-(Complex.I * (r * ‖k‖ : ℝ))) * t)) *
        ((YukawaPotential.yukawaPotential g α m r : ℝ) : ℂ)) := by
    intro r hr
    have hr' : (0:ℝ) < r := hr
    have hn : ∀ u : sphere (0 : Space) 1, ‖r • (u : Space)‖ = r := fun u => by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr']; simp
    simp_rw [hn]
    rw [integral_mul_const, sphere_wave]
  rw [setIntegral_congr_fun measurableSet_Ioi hin]
  rcases eq_or_ne k 0 with rfl | hk
  · -- k = 0
    have hpt : ∀ r ∈ Ioi (0:ℝ), (r ^ 2 : ℝ) • (((2 * π : ℝ) • ∫ t in Ioo (-1:ℝ) 1,
        Complex.exp ((-(Complex.I * (r * ‖(0 : Space)‖ : ℝ))) * t)) *
        ((YukawaPotential.yukawaPotential g α m r : ℝ) : ℂ)) =
        (((-g ^ 2 * (4 * π)) * (r ^ (1:ℝ) * Real.exp (-a * r ^ (1:ℝ))) : ℝ) : ℂ) := by
      intro r hr
      have hr' : (0:ℝ) < r := hr
      simp only [norm_zero, mul_zero, Complex.ofReal_zero, neg_zero, zero_mul, Complex.exp_zero,
        integral_const, Measure.real, Measure.restrict_apply MeasurableSet.univ, univ_inter,
        Real.volume_Ioo, Real.rpow_one, YukawaPotential.yukawaPotential]
      norm_num
      rw [ha_def]
      push_cast
      field_simp
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_complex_ofReal, integral_const_mul,
      integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) ha]
    norm_num [Real.Gamma_two]
    ring
  · have hκ : 0 < ‖k‖ := norm_pos_iff.2 hk
    set κ := ‖k‖ with hκ_def
    set c1 : ℂ := -(a : ℂ) - Complex.I * κ with hc1
    set c2 : ℂ := -(a : ℂ) + Complex.I * κ with hc2
    have hpt : ∀ r ∈ Ioi (0:ℝ), (r ^ 2 : ℝ) • (((2 * π : ℝ) • ∫ t in Ioo (-1:ℝ) 1,
        Complex.exp ((-(Complex.I * (r * κ : ℝ))) * t)) *
        ((YukawaPotential.yukawaPotential g α m r : ℝ) : ℂ)) =
        (2 * π * g ^ 2 / (Complex.I * κ)) * (Complex.exp (c1 * r) - Complex.exp (c2 * r)) := by
      intro r hr
      have hr' : (0:ℝ) < r := hr
      have hc : -(Complex.I * ((r * κ : ℝ) : ℂ)) ≠ 0 := by
        simp [Complex.I_ne_zero, hr'.ne', hκ.ne']
      rw [interval_exp hc]
      have e1 : Complex.exp (c1 * r) = (Real.exp (-(a * r)) : ℂ) * Complex.exp (-(Complex.I * ((r * κ : ℝ) : ℂ))) := by
        rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; rw [hc1]; push_cast; ring
      have e2 : Complex.exp (c2 * r) = (Real.exp (-(a * r)) : ℂ) * Complex.exp (-(-(Complex.I * ((r * κ : ℝ) : ℂ)))) := by
        rw [Complex.ofReal_exp, ← Complex.exp_add]; congr 1; rw [hc2]; push_cast; ring
      rw [e1, e2]
      simp only [YukawaPotential.yukawaPotential, Complex.real_smul]
      rw [show α * m * r = a * r by rw [ha_def]]
      push_cast
      have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
      have hr2 : (r : ℂ) ≠ 0 := by exact_mod_cast hr'.ne'
      field_simp
    have h1 : c1.re < 0 := by simp [hc1]; linarith
    have h2 : c2.re < 0 := by simp [hc2]; linarith
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
      integral_sub (integrableOn_exp_mul_complex_Ioi h1 0) (integrableOn_exp_mul_complex_Ioi h2 0),
      integral_exp_mul_complex_Ioi h1, integral_exp_mul_complex_Ioi h2]
    have hc1' : c1 ≠ 0 := fun h => by simp [h] at h1
    have hc2' : c2 ≠ 0 := fun h => by simp [h] at h2
    have hκ' : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ.ne'
    have hden : ((κ ^ 2 + a ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : κ ^ 2 + a ^ 2 ≠ 0)
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [hc1, hc2] at *
    push_cast at hden ⊢
    field_simp
    ring_nf
    linear_combination (-4 * (g : ℂ) ^ 2 * (κ : ℂ) ^ 3 * Complex.I) * Complex.I_sq

end YKFT

open YukawaPotential in
theorem solution (g α m : ℝ) (hα : 0 < α) (hm : 0 < m)
    (k : EuclideanSpace ℝ (Fin 3)) :
    ∫ x : EuclideanSpace ℝ (Fin 3),
        Complex.exp (-(Complex.I * (inner ℝ k x : ℝ))) * ((yukawaPotential g α m ‖x‖ : ℝ) : ℂ) =
      ((-g ^ 2 * (4 * Real.pi / (‖k‖ ^ 2 + (α * m) ^ 2)) : ℝ) : ℂ) :=
  YKFT.ft g α m hα hm k
