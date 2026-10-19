-- Prove2me | solution 1 for UnphysicalHilbert.eq29_erf_tan_coordinate_change
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T05:52:06.045439+00:00
-- url     : https://prove2.me/submissions/00f770dc-f85b-4f5a-82ba-4937208cbdcb

import Mathlib
import Definitions.Def_UnphysicalHilbert_Position

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
theorem solution :
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
