-- Prove2me | solution 1 for UnphysicalHilbert.prop24_change_of_variables_unitary
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:10:57.506868+00:00
-- url     : https://prove2.me/submissions/9567d6e2-0a7a-494e-95ef-8ba98ff61c30

import Definitions.Def_UnphysicalHilbert_Position

namespace UnphysicalHilbert

open MeasureTheory

namespace P24Aux

variable {f : ℝ ≃ ℝ}

lemma symm_diffeo (hf : IsOrientationPreservingDiffeo f) :
    IsOrientationPreservingDiffeo f.symm := by
  refine ⟨hf.2.1, by simpa using hf.1, ?_⟩
  intro a b hab
  by_contra h
  push Not at h
  have := hf.2.2.monotone h
  simp at this
  linarith

lemma hasDeriv (hf : IsOrientationPreservingDiffeo f) (x : ℝ) :
    HasDerivAt f (deriv f x) x :=
  ((hf.1.differentiable (by simp)) x).hasDerivAt

lemma deriv_cont (hf : IsOrientationPreservingDiffeo f) : Continuous (deriv f) :=
  hf.1.continuous_deriv (by simp)

lemma chain (hf : IsOrientationPreservingDiffeo f) (y : ℝ) :
    deriv f (f.symm y) * deriv f.symm y = 1 := by
  have h1 := (hasDeriv hf (f.symm y)).comp y (hasDeriv (symm_diffeo hf) y)
  have h2 : (f ∘ f.symm) = id := by funext z; simp
  rw [h2] at h1
  exact h1.unique (hasDerivAt_id y)

lemma abs_deriv_symm_pos (hf : IsOrientationPreservingDiffeo f) (y : ℝ) :
    0 < |deriv f.symm y| := by
  apply abs_pos.mpr
  intro h
  have := chain hf y
  rw [h, mul_zero] at this
  exact zero_ne_one this

lemma key (hf : IsOrientationPreservingDiffeo f) (F : ℝ → ENNReal) :
    ∫⁻ y, ENNReal.ofReal |deriv f.symm y| * F (f.symm y) = ∫⁻ x, F x := by
  have := lintegral_image_eq_lintegral_abs_deriv_mul (f := f.symm) (s := Set.univ)
    MeasurableSet.univ (fun y _ => (hasDeriv (symm_diffeo hf) y).hasDerivWithinAt)
    (f.symm.injective.injOn) F
  rw [Set.image_univ_of_surjective f.symm.surjective, Measure.restrict_univ] at this
  exact this.symm

lemma meas_symm (hf : IsOrientationPreservingDiffeo f) : Measurable f.symm :=
  (symm_diffeo hf).1.continuous.measurable

lemma qmp (hf : IsOrientationPreservingDiffeo f) :
    Measure.QuasiMeasurePreserving f.symm volume volume := by
  refine ⟨meas_symm hf, ?_⟩
  refine Measure.AbsolutelyContinuous.mk fun N hN h0 => ?_
  rw [Measure.map_apply (meas_symm hf) hN]
  have hk := key hf (N.indicator 1)
  rw [lintegral_indicator_one hN, h0] at hk
  have hmeas : Measurable fun y => ENNReal.ofReal |deriv f.symm y| * N.indicator 1 (f.symm y) :=
    (ENNReal.measurable_ofReal.comp (deriv_cont (symm_diffeo hf)).measurable.abs).mul
      ((measurable_one.indicator hN).comp (meas_symm hf))
  rw [lintegral_eq_zero_iff hmeas] at hk
  have hae : ∀ᵐ y ∂(volume : Measure ℝ), f.symm y ∉ N := by
    filter_upwards [hk] with y hy
    simp only [Pi.zero_apply, mul_eq_zero, ENNReal.ofReal_eq_zero] at hy
    rcases hy with hy | hy
    · exact absurd hy (not_le.mpr (abs_deriv_symm_pos hf y))
    · intro hyN
      simp [Set.indicator_of_mem (show f.symm y ∈ N from hyN)] at hy
  rw [ae_iff] at hae
  simpa [Set.preimage] using hae

lemma enorm_pt (a : ℂ) (r : ℝ) (hr : 0 ≤ r) :
    ‖a * (Real.sqrt r : ℂ)‖ₑ ^ (2 : ℝ) = ENNReal.ofReal r * ‖a‖ₑ ^ (2 : ℝ) := by
  rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), mul_comm]
  congr 1
  rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg r),
    ENNReal.rpow_two, ← ENNReal.ofReal_pow (Real.sqrt_nonneg r), Real.sq_sqrt hr]

lemma aesm (hf : IsOrientationPreservingDiffeo f) {ψ : ℝ → ℂ}
    (hψ : AEStronglyMeasurable ψ volume) :
    AEStronglyMeasurable (changeOfVariables f ψ) volume := by
  unfold changeOfVariables
  refine (hψ.comp_quasiMeasurePreserving (qmp hf)).mul ?_
  exact (Complex.continuous_ofReal.comp
    (Real.continuous_sqrt.comp (deriv_cont (symm_diffeo hf)).abs)).aestronglyMeasurable

lemma eLpNorm_eq (hf : IsOrientationPreservingDiffeo f) (ψ : ℝ → ℂ) :
    eLpNorm (changeOfVariables f ψ) 2 volume = eLpNorm ψ 2 volume := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp)]
  congr 1
  simp only [ENNReal.toReal_ofNat]
  unfold changeOfVariables
  simp_rw [enorm_pt _ _ (abs_nonneg _)]
  exact key hf (fun x => ‖ψ x‖ₑ ^ (2 : ℝ))

lemma memLp (hf : IsOrientationPreservingDiffeo f) (ψ : Lp ℂ 2 (volume : Measure ℝ)) :
    MemLp (changeOfVariables f (ψ : ℝ → ℂ)) 2 volume :=
  ⟨aesm hf (Lp.aestronglyMeasurable ψ), by rw [eLpNorm_eq hf]; exact Lp.eLpNorm_lt_top ψ⟩

lemma congr_ae (hf : IsOrientationPreservingDiffeo f) {ψ χ : ℝ → ℂ} (h : ψ =ᵐ[volume] χ) :
    changeOfVariables f ψ =ᵐ[volume] changeOfVariables f χ := by
  have := (qmp hf).ae_eq_comp h
  filter_upwards [this] with y hy
  simp only [changeOfVariables, Function.comp_apply] at hy ⊢
  rw [hy]

noncomputable def V (hf : IsOrientationPreservingDiffeo f) :
    Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun ψ := (memLp hf ψ).toLp _
  map_add' ψ χ := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp hf (ψ + χ)), Lp.coeFn_add ((memLp hf ψ).toLp _)
      ((memLp hf χ).toLp _), MemLp.coeFn_toLp (memLp hf ψ), MemLp.coeFn_toLp (memLp hf χ),
      congr_ae hf (Lp.coeFn_add ψ χ)] with y h1 h2 h3 h4 h5
    rw [h1, h2, Pi.add_apply, h3, h4, h5]
    simp [changeOfVariables, add_mul]
  map_smul' c ψ := by
    rw [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (memLp hf (c • ψ)), Lp.coeFn_smul c ((memLp hf ψ).toLp _),
      MemLp.coeFn_toLp (memLp hf ψ), congr_ae hf (Lp.coeFn_smul c ψ)] with y h1 h2 h3 h5
    rw [h1, h2, Pi.smul_apply, h3, h5]
    simp [changeOfVariables, mul_assoc]
  norm_map' ψ := by
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [Lp.norm_toLp, eLpNorm_eq hf, Lp.norm_def]

lemma V_ae (hf : IsOrientationPreservingDiffeo f) (ψ : Lp ℂ 2 (volume : Measure ℝ)) :
    (V hf ψ : ℝ → ℂ) =ᵐ[volume] changeOfVariables f (ψ : ℝ → ℂ) :=
  MemLp.coeFn_toLp (memLp hf ψ)

lemma inv_pt (hf : IsOrientationPreservingDiffeo f) (χ : ℝ → ℂ) (y : ℝ) :
    changeOfVariables f (changeOfVariables f.symm χ) y = χ y := by
  simp only [changeOfVariables, Equiv.symm_symm, Equiv.apply_symm_apply]
  rw [mul_assoc, ← Complex.ofReal_mul, ← Real.sqrt_mul (abs_nonneg _), ← abs_mul, chain hf y]
  simp

lemma V_surj (hf : IsOrientationPreservingDiffeo f) : Function.Surjective (V hf) := by
  intro χ
  refine ⟨V (symm_diffeo hf) χ, ?_⟩
  apply Lp.ext
  filter_upwards [V_ae hf (V (symm_diffeo hf) χ), congr_ae hf (V_ae (symm_diffeo hf) χ)]
    with y h1 h2
  rw [h1, h2, inv_pt hf]

end P24Aux


end UnphysicalHilbert

open MeasureTheory UnphysicalHilbert

theorem solution (f : ℝ ≃ ℝ) (hf : IsOrientationPreservingDiffeo f) :
    ∃ U : Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ),
      ∀ ψ : Lp ℂ 2 (volume : Measure ℝ),
        (U ψ : ℝ → ℂ) =ᵐ[volume] changeOfVariables f (ψ : ℝ → ℂ) :=
  ⟨LinearIsometryEquiv.ofSurjective (P24Aux.V hf) (P24Aux.V_surj hf), P24Aux.V_ae hf⟩

