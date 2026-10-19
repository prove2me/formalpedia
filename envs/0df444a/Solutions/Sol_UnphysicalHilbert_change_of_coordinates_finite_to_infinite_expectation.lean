-- Prove2me | solution 1 for UnphysicalHilbert.change_of_coordinates_finite_to_infinite_expectation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:11:09.313322+00:00
-- url     : https://prove2.me/submissions/5857a3ab-dbc2-4aba-926f-8bbde6b57ca5

import Mathlib
import Definitions.Def_UnphysicalHilbert_Position

section E29

open MeasureTheory Real UnphysicalHilbert Filter Topology
open scoped ContDiff

namespace UHErf

noncomputable def I (x : ℝ) : ℝ := ∫ t in (0:ℝ)..x, exp (-t ^ 2)

lemma cont_g : Continuous (fun t : ℝ => exp (-t ^ 2)) := by fun_prop

lemma I_deriv (x : ℝ) : HasDerivAt I (exp (-x ^ 2)) x :=
  (cont_g.integral_hasStrictDerivAt 0 x).hasDerivAt

lemma I_strictMono : StrictMono I :=
  strictMono_of_deriv_pos fun x => by rw [(I_deriv x).deriv]; exact exp_pos _

lemma I_neg (x : ℝ) : I (-x) = -I x := by
  unfold I
  have h := intervalIntegral.integral_comp_neg (a := 0) (b := -x) (fun t : ℝ => exp (-t ^ 2))
  simp only [neg_neg, neg_zero, even_two, Even.neg_pow] at h
  rw [h, intervalIntegral.integral_symm]

lemma I_tendsto : Tendsto I atTop (𝓝 (√π / 2)) := by
  have h := intervalIntegral_tendsto_integral_Ioi (μ := volume) (f := fun t : ℝ => exp (-t ^ 2)) 0
    ((integrable_exp_neg_mul_sq one_pos).integrableOn.congr_fun (fun t _ => by simp) measurableSet_Ioi)
    tendsto_id
  have h2 := integral_gaussian_Ioi 1
  simp only [neg_mul, one_mul, div_one] at h2
  rw [h2] at h
  exact h

lemma I_lt (x : ℝ) : I x < √π / 2 :=
  lt_of_lt_of_le (I_strictMono (lt_add_one x)) (I_strictMono.monotone.ge_of_tendsto I_tendsto _)

lemma I_gt (x : ℝ) : -(√π / 2) < I x := by
  have := I_lt (-x); rw [I_neg] at this; linarith

lemma erf_eq (x : ℝ) : erf x = 2 / √π * I x := rfl

lemma erf_lt (x : ℝ) : erf x < 1 := by
  rw [erf_eq]; have := I_lt x; have hp : 0 < √π := sqrt_pos.mpr pi_pos
  rw [div_mul_eq_mul_div, div_lt_one hp]; linarith

lemma erf_gt (x : ℝ) : -1 < erf x := by
  rw [erf_eq]; have := I_gt x; have hp : 0 < √π := sqrt_pos.mpr pi_pos
  rw [div_mul_eq_mul_div, lt_div_iff₀ hp]; linarith

lemma erf_deriv (x : ℝ) : HasDerivAt erf (2 / √π * exp (-x ^ 2)) x :=
  (I_deriv x).const_mul _

lemma erf_tendsto_top : Tendsto erf atTop (𝓝 1) := by
  have := I_tendsto.const_mul (2 / √π)
  have hp : 0 < √π := sqrt_pos.mpr pi_pos
  rw [show 2 / √π * (√π / 2) = 1 by field_simp] at this
  exact this

lemma erf_tendsto_bot : Tendsto erf atBot (𝓝 (-1)) := by
  have h := (erf_tendsto_top.comp tendsto_neg_atBot_atTop).neg
  refine h.congr (fun x => ?_)
  simp [Function.comp, erf_eq, I_neg]

lemma erf_contDiff : ContDiff ℝ ∞ erf := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun x => (erf_deriv x).differentiableAt, ?_⟩
  have : deriv erf = fun x => 2 / √π * exp (-x ^ 2) := funext fun x => (erf_deriv x).deriv
  rw [this]; fun_prop

lemma theta_mem (x : ℝ) : π / 2 * erf x ∈ Set.Ioo (-(π / 2)) (π / 2) := by
  have h1 := erf_lt x; have h2 := erf_gt x; have hp := pi_pos
  constructor <;> nlinarith

lemma cos_theta_ne (x : ℝ) : cos (π / 2 * erf x) ≠ 0 :=
  (cos_pos_of_mem_Ioo (theta_mem x)).ne'

lemma g_deriv (x : ℝ) : HasDerivAt erfTanCoordinate
    (1 / cos (π / 2 * erf x) ^ 2 * (π / 2 * (2 / √π * exp (-x ^ 2)))) x :=
  (hasDerivAt_tan (cos_theta_ne x)).comp x ((erf_deriv x).const_mul (π / 2))

lemma g_deriv_pos (x : ℝ) : 0 < 1 / cos (π / 2 * erf x) ^ 2 * (π / 2 * (2 / √π * exp (-x ^ 2))) := by
  have := cos_theta_ne x
  have hp := pi_pos
  have : 0 < √π := sqrt_pos.mpr pi_pos
  positivity

lemma g_contDiff : ContDiff ℝ ∞ erfTanCoordinate := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact (contDiffAt_tan.mpr (cos_theta_ne x)).comp x
    ((contDiff_const.mul erf_contDiff).contDiffAt)

lemma g_strictMono : StrictMono erfTanCoordinate :=
  strictMono_of_deriv_pos fun x => by rw [(g_deriv x).deriv]; exact g_deriv_pos x

lemma g_surj : Function.Surjective erfTanCoordinate := by
  intro y
  set θ := arctan y
  have hθ1 := neg_pi_div_two_lt_arctan y
  have hθ2 := arctan_lt_pi_div_two y
  set c := θ / (π / 2)
  have hp := pi_pos
  have hc1 : -1 < c := by rw [lt_div_iff₀ (by positivity)]; linarith
  have hc2 : c < 1 := by rw [div_lt_iff₀ (by positivity)]; linarith
  obtain ⟨a, ha⟩ := (erf_tendsto_bot.eventually (gt_mem_nhds hc1)).exists
  obtain ⟨b, hb⟩ := (erf_tendsto_top.eventually (lt_mem_nhds hc2)).exists
  have hcont : Continuous erf := erf_contDiff.continuous
  obtain ⟨x, hx⟩ := intermediate_value_univ a b hcont ⟨ha.le, hb.le⟩
  refine ⟨x, ?_⟩
  simp only [erfTanCoordinate, hx, c]
  rw [mul_div_cancel₀ _ (by positivity : π / 2 ≠ 0), tan_arctan]

end UHErf

open UHErf in
theorem eq29_sol :
    ∃ f : ℝ ≃ ℝ, (f : ℝ → ℝ) = erfTanCoordinate ∧ IsOrientationPreservingDiffeo f ∧
      ∀ x : ℝ, ∫ t in (0 : ℝ)..erfTanCoordinate x, lorentzianWave t ^ 2 =
        ∫ t in (0 : ℝ)..x, gaussianWave t ^ 2 := by
  set e := StrictMono.orderIsoOfSurjective erfTanCoordinate g_strictMono g_surj
  set hm : ℝ ≃ₜ ℝ := e.toHomeomorph
  refine ⟨e.toEquiv, rfl, ⟨g_contDiff, ?_, g_strictMono⟩, fun x => ?_⟩
  · have := hm.contDiff_symm_deriv (n := ∞) (fun x => (g_deriv_pos x).ne') g_deriv g_contDiff
    exact this
  · have h1 : ∀ t, lorentzianWave t ^ 2 = π⁻¹ * (1 / (1 + t ^ 2)) := by
      intro t; unfold lorentzianWave
      rw [div_pow, sq_sqrt (by positivity)]; field_simp; ring
    have h2 : ∀ t, gaussianWave t ^ 2 = (√π)⁻¹ * exp (-t ^ 2) := by
      intro t; unfold gaussianWave
      rw [sq_sqrt (by positivity)]; ring
    simp_rw [h1, h2]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_one_div_one_add_sq, arctan_zero, sub_zero]
    unfold erfTanCoordinate
    rw [arctan_tan (theta_mem x).1 (theta_mem x).2, erf_eq]
    unfold I
    have hp : 0 < √π := sqrt_pos.mpr pi_pos
    field_simp

end E29

section E27

open MeasureTheory Real UnphysicalHilbert

lemma gw_sq (x : ℝ) : gaussianWave x ^ 2 = exp (-x ^ 2) / √π := by
  unfold gaussianWave
  rw [sq_sqrt (by positivity)]

lemma lw_sq (y : ℝ) : lorentzianWave y ^ 2 = π⁻¹ * (1 + y ^ 2)⁻¹ := by
  unfold lorentzianWave
  rw [div_pow, sq_sqrt (by positivity)]
  field_simp
  ring

theorem eq27_sol :
    ∫ x, gaussianWave x ^ 2 = 1 ∧ ∫ y, lorentzianWave y ^ 2 = 1 ∧
    (∀ n : ℕ, Integrable (fun x : ℝ => |x| ^ n * gaussianWave x ^ 2)) ∧
    (∀ n : ℕ, 2 ≤ n → ¬ Integrable (fun y : ℝ => |y| ^ n * lorentzianWave y ^ 2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp_rw [gw_sq]
    rw [integral_div]
    have := integral_gaussian 1
    simp only [neg_mul, one_mul, div_one] at this
    rw [this]
    exact div_self (sqrt_pos.mpr pi_pos).ne'
  · simp_rw [lw_sq]
    rw [integral_const_mul, integral_univ_inv_one_add_sq, inv_mul_cancel₀ pi_pos.ne']
  · intro n
    have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1) one_pos
      (s := ((n : ℕ) : ℝ)) (by have := n.cast_nonneg (α := ℝ); linarith)
    simp_rw [rpow_natCast] at h
    have h2 := (h.abs).div_const (√π)
    refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only
    rw [gw_sq, abs_mul, abs_pow, abs_of_pos (exp_pos _)]
    ring_nf
  · intro n hn hint
    have h1 : IntegrableOn (fun y : ℝ => |y| ^ n * lorentzianWave y ^ 2) (Set.Ioi 1) :=
      hint.integrableOn
    have h2 : IntegrableOn (fun _ : ℝ => (2 * π)⁻¹) (Set.Ioi 1) := by
      refine h1.mono' (by fun_prop) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have hy1 : (1:ℝ) < y := hy
      rw [Real.norm_eq_abs, abs_of_pos (by positivity), lw_sq, abs_of_pos (by linarith)]
      have hyn : y ^ 2 ≤ y ^ n := pow_le_pow_right₀ hy1.le hn
      have hp := pi_pos
      rw [show (2 * π)⁻¹ = π⁻¹ * (1 + y ^ 2)⁻¹ * ((1 + y ^ 2) / 2) by field_simp]
      rw [show y ^ n * (π⁻¹ * (1 + y ^ 2)⁻¹) = π⁻¹ * (1 + y ^ 2)⁻¹ * y ^ n by ring]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith
    rw [integrableOn_const_iff] at h2
    rcases h2 with h2 | h2
    · have : (2 * π)⁻¹ ≠ 0 := by positivity
      exact this (enorm_eq_zero.mp h2)
    · simp at h2

end E27

section P24

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

theorem prop24_sol (f : ℝ ≃ ℝ) (hf : IsOrientationPreservingDiffeo f) :
    ∃ U : Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ),
      ∀ ψ : Lp ℂ 2 (volume : Measure ℝ),
        (U ψ : ℝ → ℂ) =ᵐ[volume] changeOfVariables f (ψ : ℝ → ℂ) :=
  ⟨LinearIsometryEquiv.ofSurjective (P24Aux.V hf) (P24Aux.V_surj hf), P24Aux.V_ae hf⟩

end UnphysicalHilbert

end P24

namespace UnphysicalHilbert

open MeasureTheory

namespace GoalAux

lemma G_cont : Continuous gaussianWave := by
  unfold gaussianWave; fun_prop

lemma L_cont : Continuous (fun y => lorentzianWave y ^ 2) := by
  have : ∀ y, lorentzianWave y ^ 2 = Real.pi⁻¹ * (1 + y ^ 2)⁻¹ := lw_sq
  simp_rw [this]
  exact continuous_const.mul ((continuous_const.add (continuous_pow 2)).inv₀
    (fun y => ne_of_gt (by have := sq_nonneg y; show (0:ℝ) < 1 + y ^ 2; linarith)))

lemma pt_identity (f : ℝ ≃ ℝ) (hfe : (f : ℝ → ℝ) = erfTanCoordinate)
    (hf : IsOrientationPreservingDiffeo f)
    (hint : ∀ x : ℝ, ∫ t in (0 : ℝ)..erfTanCoordinate x, lorentzianWave t ^ 2 =
        ∫ t in (0 : ℝ)..x, gaussianWave t ^ 2) (y : ℝ) :
    gaussianWave (f.symm y) ^ 2 * |deriv f.symm y| = lorentzianWave y ^ 2 := by
  have hd : ∀ x, lorentzianWave (f x) ^ 2 * deriv f x = gaussianWave x ^ 2 := by
    intro x
    have h1 : HasDerivAt (fun x => ∫ t in (0 : ℝ)..f x, lorentzianWave t ^ 2)
        (lorentzianWave (f x) ^ 2 * deriv f x) x := by
      have := (intervalIntegral.integral_hasDerivAt_right
        (L_cont.intervalIntegrable 0 (f x)) (L_cont.stronglyMeasurableAtFilter _ _)
        L_cont.continuousAt).comp x (P24Aux.hasDeriv hf x)
      exact this
    have h2 : HasDerivAt (fun x => ∫ t in (0 : ℝ)..x, gaussianWave t ^ 2) (gaussianWave x ^ 2) x :=
      intervalIntegral.integral_hasDerivAt_right
        ((G_cont.pow 2).intervalIntegrable 0 x) ((G_cont.pow 2).stronglyMeasurableAtFilter _ _)
        (G_cont.pow 2).continuousAt
    have heq : (fun x => ∫ t in (0 : ℝ)..f x, lorentzianWave t ^ 2) =
        (fun x => ∫ t in (0 : ℝ)..x, gaussianWave t ^ 2) := by
      funext x; rw [hfe]; exact hint x
    rw [heq] at h1
    exact h1.unique h2
  have h := hd (f.symm y)
  rw [Equiv.apply_symm_apply] at h
  have hL : 0 < lorentzianWave y ^ 2 := by
    rw [lw_sq]; have := Real.pi_pos; positivity
  have hpos : 0 ≤ deriv f (f.symm y) := by
    by_contra hneg
    push Not at hneg
    have : lorentzianWave y ^ 2 * deriv f (f.symm y) < 0 := mul_neg_of_pos_of_neg hL hneg
    rw [h] at this
    exact absurd this (not_lt.mpr (sq_nonneg _))
  rw [← h, mul_assoc, ← abs_of_nonneg hpos, ← abs_mul, P24Aux.chain hf y]
  simp

end GoalAux


end UnphysicalHilbert

open MeasureTheory UnphysicalHilbert

theorem solution :
    ∃ f : ℝ ≃ ℝ, IsOrientationPreservingDiffeo f ∧
    ∃ U : Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ),
      (∀ g : Lp ℂ 2 (volume : Measure ℝ),
        (U g : ℝ → ℂ) =ᵐ[volume] changeOfVariables f (g : ℝ → ℂ)) ∧
    ∃ ψ : Lp ℂ 2 (volume : Measure ℝ), ‖ψ‖ = 1 ∧
      (∀ n : ℕ, Integrable (fun x : ℝ => |x| ^ n * ‖(ψ : ℝ → ℂ) x‖ ^ 2)) ∧
      ¬ Integrable (fun y : ℝ => y ^ 2 * ‖(U ψ : ℝ → ℂ) y‖ ^ 2) := by
  obtain ⟨f, hfe, hf, hint⟩ := eq29_sol
  obtain ⟨U, hU⟩ := prop24_sol f hf
  obtain ⟨hG1, -, hGmom, hLnot⟩ := eq27_sol
  set Gc : ℝ → ℂ := fun x => (gaussianWave x : ℂ) with hGc
  have hnG : ∀ x, ‖Gc x‖ ^ 2 = gaussianWave x ^ 2 := fun x => by
    simp [Gc, Complex.norm_real, sq_abs]
  have hGmeas : AEStronglyMeasurable Gc volume :=
    (Complex.continuous_ofReal.comp GoalAux.G_cont).aestronglyMeasurable
  have hGmem : MemLp Gc 2 volume := by
    rw [memLp_two_iff_integrable_sq_norm hGmeas]
    simp_rw [hnG]
    simpa using hGmom 0
  set ψ := hGmem.toLp Gc
  have hψ : (ψ : ℝ → ℂ) =ᵐ[volume] Gc := MemLp.coeFn_toLp hGmem
  refine ⟨f, hf, U, hU, ψ, ?_, ?_, ?_⟩
  · rw [Lp.norm_toLp, hGmem.eLpNorm_eq_integral_rpow_norm (by norm_num) (by simp)]
    simp only [ENNReal.toReal_ofNat]
    have : ∀ x, ‖Gc x‖ ^ (2 : ℝ) = gaussianWave x ^ 2 := fun x => by
      rw [Real.rpow_two, hnG]
    simp_rw [this, hG1]
    simp
  · intro n
    refine (hGmom n).congr ?_
    filter_upwards [hψ] with x hx
    rw [hx, hnG]
  · intro hI
    apply hLnot 2 le_rfl
    refine hI.congr ?_
    filter_upwards [hU ψ, P24Aux.congr_ae hf hψ] with y h1 h2
    rw [h1, h2]
    simp only [changeOfVariables, Gc, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
      sq_abs, Real.sq_sqrt (abs_nonneg _)]
    rw [GoalAux.pt_identity f hfe hf hint y]

