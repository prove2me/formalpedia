-- Prove2me | solution 1 for Weinberg1965.photonIndex_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-24T19:35:53.58949+00:00
-- url     : https://prove2.me/submissions/f5f0e2e7-a4a5-42a8-b3fe-cafd753c1f2f

import Mathlib
import Definitions.Def_Weinberg1965_Defs

/-! 5b1b3c65 Weinberg1965.photonIndex_closed_form (Weinberg 1965, Eqs. (2.14)-(2.16)).
Reuses the sphere-integral machinery of 0bcac0f0 (graviton case): polar decomposition turns
sphere moments into Gaussian integrals, a power series gives `∫ dσ/(E-⟪p,u⟫)^2 = 4π/(E^2-‖p‖^2)`,
Feynman parametrisation reduces the two-denominator kernel to a 1-D integral evaluated in closed
form with a log antiderivative, and the result is matched to `photonKernel (relVel ..)`.
No `Theorems.*` module is imported. -/

set_option autoImplicit false

namespace WeinbergBuild

open MeasureTheory Real Set Weinberg1965

theorem polar_mul (F : Vec3 → ℝ) (g : ℝ → ℝ) :
    ∫ x : Vec3, F (‖x‖⁻¹ • x) * g ‖x‖ =
      (∫ u : Metric.sphere (0 : Vec3) 1, F u ∂(volume.toSphere)) *
        ∫ r in Ioi (0 : ℝ), r ^ 2 * g r := by
  have h1 : ∫ x : Vec3, F (‖x‖⁻¹ • x) * g ‖x‖ =
      ∫ x : ({(0 : Vec3)}ᶜ : Set Vec3), F (‖(x : Vec3)‖⁻¹ • (x : Vec3)) * g ‖(x : Vec3)‖
        ∂(volume.comap Subtype.val) := by
    rw [integral_subtype_comap (measurableSet_singleton _).compl
      (fun x : Vec3 => F (‖x‖⁻¹ • x) * g ‖x‖), restrict_compl_singleton]
  have h2 := (Measure.measurePreserving_homeomorphUnitSphereProd (volume : Measure Vec3)).integral_comp
    (Homeomorph.measurableEmbedding _) (fun z => F (z.1 : Vec3) * g (z.2 : ℝ))
  simp only [homeomorphUnitSphereProd_apply_fst_coe, homeomorphUnitSphereProd_apply_snd_coe] at h2
  rw [h1, h2]
  refine (integral_prod_mul (fun u : Metric.sphere (0 : Vec3) 1 => F u)
    (fun r : Ioi (0:ℝ) => g r)).trans ?_
  congr 1
  simp only [Measure.volumeIoiPow, finrank_euclideanSpace_fin, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul,
    integral_subtype_comap measurableSet_Ioi fun a ↦ Real.toNNReal (a ^ (3 - 1)) • g a,
    setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_]
  · rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg (le_of_lt hx) _)]
    norm_num
  · exact (measurable_subtype_coe.pow_const _).real_toNNReal

theorem gauss3 (f : ℝ → ℝ) :
    ∫ x : Vec3, f (x 0) * exp (-‖x‖ ^ 2) = (∫ t : ℝ, f t * exp (-t ^ 2)) * π := by
  have e := (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).integral_comp'
    (fun y : Fin 3 → ℝ => ∏ i, (![fun t => f t * exp (-t ^ 2), fun t => exp (-t ^ 2),
      fun t => exp (-t ^ 2)] : Fin 3 → ℝ → ℝ) i (y i))
  rw [integral_fintype_prod_volume_eq_prod] at e
  have hg : ∫ t : ℝ, exp (-t ^ 2) = √π := by
    simpa using integral_gaussian 1
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, hg] at e
  rw [mul_assoc, Real.mul_self_sqrt pi_pos.le] at e
  rw [← e]
  congr 1
  ext x
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs, MeasurableEquiv.toLp_symm_apply]
  rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add]
  congr 2
  ring

theorem half_moment (j : ℕ) :
    ∫ t in Ioi (0:ℝ), t ^ j * exp (-t ^ 2) = 1 / 2 * Gamma ((j + 1) / 2) := by
  have h := integral_rpow_mul_exp_neg_rpow (p := 2) (q := (j : ℝ)) two_pos
    (by have : (0:ℝ) ≤ j := Nat.cast_nonneg j; linarith)
  simpa only [Real.rpow_natCast, Real.rpow_two] using h

theorem full_moment (j : ℕ) :
    ∫ t : ℝ, t ^ j * exp (-t ^ 2) = (1 + (-1) ^ j) * (1 / 2 * Gamma ((j + 1) / 2)) := by
  have hint : Integrable (fun t : ℝ => t ^ j * exp (-t ^ 2)) := by
    have := integrable_rpow_mul_exp_neg_mul_sq (b := 1) one_pos (s := (j : ℝ))
      (by have : (0:ℝ) ≤ j := Nat.cast_nonneg j; linarith)
    simpa only [Real.rpow_natCast, neg_mul, one_mul] using this
  rw [← intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn]
  have h2 : ∫ t in Iic (0:ℝ), t ^ j * exp (-t ^ 2) =
      (-1) ^ j * ∫ t in Ioi (0:ℝ), t ^ j * exp (-t ^ 2) := by
    rw [← integral_const_mul]
    have := integral_comp_neg_Ioi (0:ℝ) (fun t : ℝ => t ^ j * exp (-t ^ 2))
    rw [neg_zero] at this
    rw [← this]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp only [neg_sq, neg_pow t j]
    ring
  rw [h2, half_moment]
  ring

theorem rot_integral (p : Vec3) (Φ : ℝ → ℝ → ℝ) :
    ∫ x : Vec3, Φ (inner ℝ p x) ‖x‖ = ∫ x : Vec3, Φ (‖p‖ * x 0) ‖x‖ := by
  set e0 : Vec3 := EuclideanSpace.single 0 1
  set R := Submodule.reflection (ℝ ∙ (‖p‖ • e0 - p))ᗮ
  have hR : R (‖p‖ • e0) = p := by
    apply Submodule.reflection_sub
    simp [e0, norm_smul]
  have key : ∀ x : Vec3, inner ℝ p (R x) = ‖p‖ * x 0 := by
    intro x
    calc inner ℝ p (R x) = inner ℝ (R (‖p‖ • e0)) (R x) := by rw [hR]
      _ = ‖p‖ * x 0 := by
        rw [LinearIsometryEquiv.inner_map_map, real_inner_smul_left,
          EuclideanSpace.inner_single_left]
        simp
  have := (R.measurePreserving).integral_comp R.toHomeomorph.measurableEmbedding
    (fun x => Φ (inner ℝ p x) ‖x‖)
  simp only [key, LinearIsometryEquiv.norm_map] at this
  exact this.symm

theorem sphere_moment (p : Vec3) (j : ℕ) :
    ∫ u : Metric.sphere (0:Vec3) 1, inner ℝ p (u:Vec3) ^ j ∂(volume.toSphere) =
      2 * π * (1 + (-1) ^ j) * ‖p‖ ^ j / (j + 1) := by
  have hP := polar_mul (fun v => inner ℝ p v ^ j) (fun r => r ^ j * exp (-r ^ 2))
  have hL : ∫ x : Vec3, inner ℝ p (‖x‖⁻¹ • x) ^ j * (‖x‖ ^ j * exp (-‖x‖ ^ 2)) =
      ∫ x : Vec3, inner ℝ p x ^ j * exp (-‖x‖ ^ 2) := by
    congr 1
    ext x
    by_cases hx : x = 0
    · simp only [hx, norm_zero, inv_zero, smul_zero, inner_zero_right]
      rw [← mul_assoc, ← mul_pow, mul_zero]
    have : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    rw [real_inner_smul_right, mul_pow, inv_pow]
    field_simp
  have hR := rot_integral p (fun a r => a ^ j * exp (-r ^ 2))
  have hG := gauss3 (fun t => (‖p‖ * t) ^ j)
  have hB : ∫ r in Ioi (0:ℝ), r ^ 2 * (r ^ j * exp (-r ^ 2)) =
      1 / 2 * Gamma ((((j + 2 : ℕ) : ℝ) + 1) / 2) := by
    rw [← half_moment (j + 2)]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    ring
  have hA : ∫ t : ℝ, (‖p‖ * t) ^ j * exp (-t ^ 2) =
      ‖p‖ ^ j * ((1 + (-1) ^ j) * (1 / 2 * Gamma ((j + 1) / 2))) := by
    simp_rw [mul_pow, mul_assoc]
    rw [integral_const_mul, full_moment]
  have hΓs : Gamma ((((j + 2 : ℕ) : ℝ) + 1) / 2) = (j + 1) / 2 * Gamma ((j + 1) / 2) := by
    rw [show (((j + 2 : ℕ) : ℝ) + 1) / 2 = (j + 1) / 2 + 1 by push_cast; ring]
    exact Real.Gamma_add_one (by positivity)
  have hΓ : Gamma ((j + 1) / 2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  simp only at hP hR hG
  rw [hL, hR, hG, hA, hB, hΓs] at hP
  set M := ∫ u : Metric.sphere (0:Vec3) 1, inner ℝ p (u:Vec3) ^ j ∂(volume.toSphere)
  have hj : (j : ℝ) + 1 ≠ 0 := by positivity
  rw [eq_div_iff hj]
  apply mul_right_cancel₀ hΓ
  linear_combination (-4) * hP

theorem geom_sq (E a : ℝ) (hE : 0 < E) (ha : |a| < E) :
    HasSum (fun j : ℕ => ((j : ℝ) + 1) / E ^ (j + 2) * a ^ j) (1 / (E - a) ^ 2) := by
  have hr' : |a / E| < 1 := by
    rw [abs_div, abs_of_pos hE, div_lt_one hE]; exact ha
  have hr : ‖a / E‖ < 1 := by rwa [Real.norm_eq_abs]
  have h := ((hasSum_coe_mul_geometric_of_norm_lt_one hr).add
    (hasSum_geometric_of_abs_lt_one hr')).mul_left (1 / E ^ 2)
  have hEa : E - a ≠ 0 := by
    have := le_abs_self a; intro h; linarith
  have e1 : (fun j : ℕ => ((j : ℝ) + 1) / E ^ (j + 2) * a ^ j) =
      fun i : ℕ => 1 / E ^ 2 * ((i : ℝ) * (a / E) ^ i + (a / E) ^ i) := by
    funext j
    rw [div_pow, pow_add]
    field_simp
  have e2 : 1 / (E - a) ^ 2 = 1 / E ^ 2 * (a / E / (1 - a / E) ^ 2 + (1 - a / E)⁻¹) := by
    rw [one_sub_div hE.ne', inv_div]
    field_simp
    ring
  rw [e1, e2]
  exact h

theorem sphere_J (E : ℝ) (p : Vec3) (h : ‖p‖ < E) :
    ∫ u : Metric.sphere (0:Vec3) 1, 1 / (E - inner ℝ p (u:Vec3)) ^ 2 ∂(volume.toSphere) =
      4 * π / (E ^ 2 - ‖p‖ ^ 2) := by
  have hE : 0 < E := lt_of_le_of_lt (norm_nonneg p) h
  have hbd : ∀ u : Metric.sphere (0:Vec3) 1, |inner ℝ p (u:Vec3)| ≤ ‖p‖ := fun u => by
    have := abs_real_inner_le_norm p (u:Vec3)
    rwa [norm_eq_of_mem_sphere, mul_one] at this
  set F : ℕ → Metric.sphere (0:Vec3) 1 → ℝ :=
    fun j u => ((j : ℝ) + 1) / E ^ (j + 2) * inner ℝ p (u:Vec3) ^ j with hFdef
  have hF : ∀ j, Integrable (F j) (volume.toSphere) := fun j =>
    (by fun_prop : Continuous (F j)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hpt : ∀ u : Metric.sphere (0:Vec3) 1,
      HasSum (fun j => F j u) (1 / (E - inner ℝ p (u:Vec3)) ^ 2) := fun u =>
    geom_sq E _ hE (lt_of_le_of_lt (hbd u) h)
  have hs0 : |‖p‖| < E := by rwa [abs_of_nonneg (norm_nonneg p)]
  have hsum : Summable fun j => ∫ u, ‖F j u‖ ∂(volume.toSphere) := by
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg (fun u => norm_nonneg _))
      (fun j => ?_) (((geom_sq E ‖p‖ hE hs0).summable).mul_right
        ((volume : Measure Vec3).toSphere.real univ))
    calc ∫ u, ‖F j u‖ ∂(volume.toSphere)
        ≤ ∫ u : Metric.sphere (0:Vec3) 1, ((j : ℝ) + 1) / E ^ (j + 2) * ‖p‖ ^ j
            ∂(volume.toSphere) := by
          refine integral_mono (hF j).norm (integrable_const _) (fun u => ?_)
          simp only [hFdef, Real.norm_eq_abs, abs_mul, abs_pow]
          rw [abs_of_pos (by positivity : (0:ℝ) < ((j : ℝ) + 1) / E ^ (j + 2))]
          gcongr
          exact hbd u
      _ = _ := by rw [integral_const, smul_eq_mul, mul_comm]
  have H1 := hasSum_integral_of_summable_integral_norm hF hsum
  rw [integral_congr_ae (Filter.Eventually.of_forall fun u => (hpt u).tsum_eq)] at H1
  have hmom : ∀ j : ℕ, ∫ u, F j u ∂(volume.toSphere) =
      2 * π / E ^ 2 * ((‖p‖ / E) ^ j + (-(‖p‖ / E)) ^ j) := by
    intro j
    simp only [hFdef]
    rw [integral_const_mul, sphere_moment]
    have hj : (j : ℝ) + 1 ≠ 0 := by positivity
    rw [neg_div', div_pow, div_pow, neg_pow ‖p‖, pow_add]
    field_simp
  simp_rw [hmom] at H1
  have hq : |‖p‖ / E| < 1 := by
    rw [abs_div, abs_of_pos hE, div_lt_one hE]; exact hs0
  have hq' : |-(‖p‖ / E)| < 1 := by rwa [abs_neg]
  have H2 := ((hasSum_geometric_of_abs_lt_one hq).add
    (hasSum_geometric_of_abs_lt_one hq')).mul_left (2 * π / E ^ 2)
  rw [H1.unique H2]
  have h1 : E - ‖p‖ ≠ 0 := by linarith
  have h2 : E + ‖p‖ ≠ 0 := by have := norm_nonneg p; linarith
  have h3 : E ^ 2 - ‖p‖ ^ 2 ≠ 0 := by
    rw [show E ^ 2 - ‖p‖ ^ 2 = (E - ‖p‖) * (E + ‖p‖) by ring]; exact mul_ne_zero h1 h2
  have h4 : 1 - ‖p‖ / E ≠ 0 := by
    rw [sub_ne_zero]; intro h; rw [eq_div_iff hE.ne'] at h; apply h1; linarith
  rw [sub_neg_eq_add, one_add_div hE.ne', one_sub_div hE.ne', inv_div, inv_div]
  field_simp
  ring

theorem convex_pos (A B x : ℝ) (hA : 0 < A) (hB : 0 < B) (hx : x ∈ uIcc (0:ℝ) 1) :
    0 < x * A + (1 - x) * B := by
  rw [uIcc_of_le zero_le_one] at hx
  obtain ⟨h0, h1⟩ := hx
  rcases le_total A B with hAB | hAB
  · nlinarith [mul_le_mul_of_nonneg_left hAB (sub_nonneg.2 h1)]
  · nlinarith [mul_le_mul_of_nonneg_left hAB h0]

theorem affine_deriv (A B x : ℝ) :
    HasDerivAt (fun y => y * A + (1 - y) * B) (A - B) x :=
  (((hasDerivAt_id' x).mul_const A).add
    (((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id' x)).mul_const B)).congr_deriv (by ring)

theorem feynman (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    ∫ x in (0:ℝ)..1, 1 / (x * A + (1 - x) * B) ^ 2 = 1 / (A * B) := by
  have hderiv : ∀ x ∈ uIcc (0:ℝ) 1, HasDerivAt (fun x => x / (B * (x * A + (1 - x) * B)))
      (1 / (x * A + (1 - x) * B) ^ 2) x := by
    intro x hx
    have hq := convex_pos A B x hA hB hx
    refine ((hasDerivAt_id' x).div ((affine_deriv A B x).const_mul B)
      (by positivity)).congr_deriv ?_
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
  · simp only [one_mul, sub_self, zero_mul, add_zero, zero_div, sub_zero]
    rw [mul_comm]
  · apply ContinuousOn.intervalIntegrable
    exact ContinuousOn.div continuousOn_const (by fun_prop)
      (fun x hx => (pow_pos (convex_pos A B x hA hB hx) 2).ne')

theorem quad_int (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hD : a * b < c ^ 2) :
    ∫ x in (0:ℝ)..1, 1 / (a * x ^ 2 + b * (1 - x) ^ 2 + 2 * c * x * (1 - x)) =
      1 / (2 * √(c ^ 2 - a * b)) *
        log ((c + √(c ^ 2 - a * b)) / (c - √(c ^ 2 - a * b))) := by
  set d := √(c ^ 2 - a * b) with hd_def
  have hd : 0 < d := Real.sqrt_pos.2 (by linarith)
  have hd2 : d ^ 2 = c ^ 2 - a * b := Real.sq_sqrt (by linarith)
  have hdc : d < c := by nlinarith [mul_pos ha hb]
  have hcd : 0 < c - d := by linarith
  have hcd' : 0 < c + d := by linarith
  have hQ : ∀ x : ℝ, a * (a * x ^ 2 + b * (1 - x) ^ 2 + 2 * c * x * (1 - x)) =
      (x * a + (1 - x) * (c - d)) * (x * a + (1 - x) * (c + d)) := by
    intro x
    linear_combination (1 - x) ^ 2 * hd2
  have hQpos : ∀ x ∈ uIcc (0:ℝ) 1, 0 < a * x ^ 2 + b * (1 - x) ^ 2 + 2 * c * x * (1 - x) := by
    intro x hx
    have := mul_pos (convex_pos a (c - d) x ha hcd hx) (convex_pos a (c + d) x ha hcd' hx)
    rw [← hQ x] at this
    exact pos_of_mul_pos_right this ha.le
  have hderiv : ∀ x ∈ uIcc (0:ℝ) 1,
      HasDerivAt (fun x => 1 / (2 * d) * (log (x * a + (1 - x) * (c - d)) -
        log (x * a + (1 - x) * (c + d))))
      (1 / (a * x ^ 2 + b * (1 - x) ^ 2 + 2 * c * x * (1 - x))) x := by
    intro x hx
    have p1 := convex_pos a (c - d) x ha hcd hx
    have p2 := convex_pos a (c + d) x ha hcd' hx
    have hq := hQpos x hx
    refine ((((affine_deriv a (c - d) x).log p1.ne').sub
      ((affine_deriv a (c + d) x).log p2.ne')).const_mul (1 / (2 * d))).congr_deriv ?_
    rw [div_sub_div _ _ p1.ne' p2.ne']
    have key : (a - (c - d)) * (x * a + (1 - x) * (c + d)) -
        (x * a + (1 - x) * (c - d)) * (a - (c + d)) = 2 * d * a := by ring
    rw [key, ← hQ x]
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
  · simp only [one_mul, sub_self, zero_mul, add_zero, zero_add, sub_zero, mul_zero, zero_sub]
    rw [Real.log_div hcd'.ne' hcd.ne']
    ring
  · apply ContinuousOn.intervalIntegrable
    exact ContinuousOn.div continuousOn_const (by fun_prop) (fun x hx => (hQpos x hx).ne')

theorem pair_kernel (E1 E2 : ℝ) (p1 p2 : Vec3) (h1 : ‖p1‖ < E1) (h2 : ‖p2‖ < E2) :
    ∫ u : Metric.sphere (0:Vec3) 1,
        1 / ((E1 - inner ℝ p1 (u:Vec3)) * (E2 - inner ℝ p2 (u:Vec3))) ∂(volume.toSphere) =
      ∫ x in (0:ℝ)..1, 4 * π / ((x * E1 + (1 - x) * E2) ^ 2 - ‖x • p1 + (1 - x) • p2‖ ^ 2) := by
  have hA : ∀ u : Metric.sphere (0:Vec3) 1, E1 - ‖p1‖ ≤ E1 - inner ℝ p1 (u:Vec3) := fun u => by
    have := real_inner_le_norm p1 (u:Vec3)
    rw [norm_eq_of_mem_sphere, mul_one] at this; linarith
  have hB : ∀ u : Metric.sphere (0:Vec3) 1, E2 - ‖p2‖ ≤ E2 - inner ℝ p2 (u:Vec3) := fun u => by
    have := real_inner_le_norm p2 (u:Vec3)
    rw [norm_eq_of_mem_sphere, mul_one] at this; linarith
  have hk : ∀ (u : Metric.sphere (0:Vec3) 1) (x : ℝ),
      (x * E1 + (1 - x) * E2) - inner ℝ (x • p1 + (1 - x) • p2) (u:Vec3) =
        x * (E1 - inner ℝ p1 (u:Vec3)) + (1 - x) * (E2 - inner ℝ p2 (u:Vec3)) := by
    intro u x
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    ring
  have hpt : ∀ u : Metric.sphere (0:Vec3) 1,
      1 / ((E1 - inner ℝ p1 (u:Vec3)) * (E2 - inner ℝ p2 (u:Vec3))) =
        ∫ x in (0:ℝ)..1, 1 / ((x * E1 + (1 - x) * E2) -
          inner ℝ (x • p1 + (1 - x) • p2) (u:Vec3)) ^ 2 := by
    intro u
    simp only [hk]
    rw [feynman _ _ (by linarith [hA u]) (by linarith [hB u])]
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  simp only [intervalIntegral.integral_of_le zero_le_one]
  set δ := min (E1 - ‖p1‖) (E2 - ‖p2‖) with hδ
  have hδpos : 0 < δ := lt_min (by linarith) (by linarith)
  have hmeas : ((volume : Measure Vec3).toSphere).prod (volume.restrict (Ioc (0:ℝ) 1)) =
      (((volume : Measure Vec3).toSphere).prod volume).restrict (univ ×ˢ Ioc (0:ℝ) 1) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hint : Integrable (Function.uncurry fun (u : Metric.sphere (0:Vec3) 1) (x : ℝ) =>
      1 / ((x * E1 + (1 - x) * E2) - inner ℝ (x • p1 + (1 - x) • p2) (u:Vec3)) ^ 2)
      (((volume : Measure Vec3).toSphere).prod (volume.restrict (Ioc (0:ℝ) 1))) := by
    refine Integrable.mono' (integrable_const (1 / δ ^ 2)) ?_ ?_
    · apply Measurable.aestronglyMeasurable
      unfold Function.uncurry
      fun_prop
    · rw [hmeas]
      filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ioc)] with z hz
      obtain ⟨-, hz0, hz1⟩ := hz
      have hden : δ ≤ (z.2 * E1 + (1 - z.2) * E2) - inner ℝ (z.2 • p1 + (1 - z.2) • p2) (z.1:Vec3) := by
        rw [hk]
        have e1 : δ ≤ E1 - inner ℝ p1 (z.1:Vec3) := le_trans (min_le_left _ _) (hA z.1)
        have e2 : δ ≤ E2 - inner ℝ p2 (z.1:Vec3) := le_trans (min_le_right _ _) (hB z.1)
        nlinarith [mul_le_mul_of_nonneg_left e1 hz0.le,
          mul_le_mul_of_nonneg_left e2 (sub_nonneg.2 hz1)]
      simp only [Function.uncurry, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
      exact one_div_le_one_div_of_le (pow_pos hδpos 2) (pow_le_pow_left₀ hδpos.le hden 2)
  rw [integral_integral_swap hint]
  refine setIntegral_congr_fun measurableSet_Ioc (fun x hx => ?_)
  have hnorm : ‖x • p1 + (1 - x) • p2‖ < x * E1 + (1 - x) * E2 := by
    calc ‖x • p1 + (1 - x) • p2‖ ≤ ‖x • p1‖ + ‖(1 - x) • p2‖ := norm_add_le _ _
      _ = x * ‖p1‖ + (1 - x) * ‖p2‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hx.1.le,
          Real.norm_of_nonneg (sub_nonneg.2 hx.2)]
      _ < x * E1 + (1 - x) * E2 := by
        nlinarith [mul_lt_mul_of_pos_left h1 hx.1,
          mul_le_mul_of_nonneg_left h2.le (sub_nonneg.2 hx.2)]
  exact sphere_J _ _ hnorm


theorem pair_closed_ph (m1 m2 : ℝ) (p1 p2 : Vec3) (hm1 : 0 < m1) (hm2 : 0 < m2) :
    mdot m1 p1 m2 p2 *
      ∫ u : Metric.sphere (0:Vec3) 1, 1 / ((energy m1 p1 - inner ℝ p1 (u:Vec3)) *
        (energy m2 p2 - inner ℝ p2 (u:Vec3))) ∂(volume.toSphere) =
      -(2 * π) * photonKernel (relVel m1 p1 m2 p2) := by
  have hE1sq : energy m1 p1 ^ 2 = ‖p1‖ ^ 2 + m1 ^ 2 := Real.sq_sqrt (by positivity)
  have hE2sq : energy m2 p2 ^ 2 = ‖p2‖ ^ 2 + m2 ^ 2 := Real.sq_sqrt (by positivity)
  have hE1 : ‖p1‖ < energy m1 p1 :=
    (Real.lt_sqrt (norm_nonneg _)).2 (by nlinarith)
  have hE2 : ‖p2‖ < energy m2 p2 :=
    (Real.lt_sqrt (norm_nonneg _)).2 (by nlinarith)
  rw [pair_kernel _ _ _ _ hE1 hE2]
  set E1 := energy m1 p1 with hE1def
  set E2 := energy m2 p2 with hE2def
  set c := E1 * E2 - inner ℝ p1 p2 with hcdef
  have hmdot : mdot m1 p1 m2 p2 = -c := by
    rw [mdot, ← hE1def, ← hE2def, hcdef]; ring
  have hEE : E1 * E2 = √((‖p1‖ ^ 2 + m1 ^ 2) * (‖p2‖ ^ 2 + m2 ^ 2)) := by
    rw [Real.sqrt_mul (by positivity)]
    rfl
  have hs : ‖p1‖ * ‖p2‖ + m1 * m2 ≤ E1 * E2 := by
    rw [hEE, Real.le_sqrt (by positivity) (by positivity)]
    nlinarith [sq_nonneg (‖p1‖ * m2 - m1 * ‖p2‖)]
  have hcm : m1 * m2 ≤ c := by
    have := real_inner_le_norm p1 p2
    rw [hcdef]; linarith
  have hc : 0 < c := lt_of_lt_of_le (mul_pos hm1 hm2) hcm
  have hQ : ∀ x : ℝ, (x * E1 + (1 - x) * E2) ^ 2 - ‖x • p1 + (1 - x) • p2‖ ^ 2 =
      m1 ^ 2 * x ^ 2 + m2 ^ 2 * (1 - x) ^ 2 + 2 * c * x * (1 - x) := by
    intro x
    rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      mul_pow, mul_pow, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs, hcdef]
    linear_combination x ^ 2 * hE1sq + (1 - x) ^ 2 * hE2sq
  have hI : ∫ x in (0:ℝ)..1, 4 * π / ((x * E1 + (1 - x) * E2) ^ 2 -
      ‖x • p1 + (1 - x) • p2‖ ^ 2) =
      4 * π * ∫ x in (0:ℝ)..1, 1 / (m1 ^ 2 * x ^ 2 + m2 ^ 2 * (1 - x) ^ 2 +
        2 * c * x * (1 - x)) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext x
    rw [hQ x, mul_one_div]
  rw [hI, hmdot]
  have hab : m1 ^ 2 * m2 ^ 2 ≤ c ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hcm 2
  have hrel : relVel m1 p1 m2 p2 = √(1 - m1 ^ 2 * m2 ^ 2 / c ^ 2) := by
    rw [relVel, hmdot, neg_sq]
  rw [hrel]
  rcases hab.lt_or_eq with hlt | heq
  · rw [quad_int _ _ _ (by positivity) (by positivity) hc hlt]
    set d := √(c ^ 2 - m1 ^ 2 * m2 ^ 2) with hd_def
    have hd : 0 < d := Real.sqrt_pos.2 (by linarith)
    have hd2 : d ^ 2 = c ^ 2 - m1 ^ 2 * m2 ^ 2 := Real.sq_sqrt (by linarith)
    have hdc : d < c := by
      rw [hd_def, Real.sqrt_lt' hc]
      have : 0 < m1 ^ 2 * m2 ^ 2 := by positivity
      linarith
    have hβ : √(1 - m1 ^ 2 * m2 ^ 2 / c ^ 2) = d / c := by
      rw [← Real.sqrt_sq (div_pos hd hc).le]
      congr 1
      field_simp
      linear_combination -hd2
    rw [hβ]
    have hβ0 : d / c ≠ 0 := (div_pos hd hc).ne'
    have hR : (1 + d / c) / (1 - d / c) = (c + d) / (c - d) := by
      have : c - d ≠ 0 := by linarith
      field_simp
    rw [photonKernel, if_neg hβ0, hR, inv_div]
    field_simp
    ring
  · have hcm' : c = m1 * m2 := by
      exact (pow_left_inj₀ hc.le (by positivity) two_ne_zero).1 (by rw [mul_pow]; exact heq.symm)
    have hQ' : ∀ x : ℝ, m1 ^ 2 * x ^ 2 + m2 ^ 2 * (1 - x) ^ 2 + 2 * c * x * (1 - x) =
        (x * m1 + (1 - x) * m2) ^ 2 := by
      intro x; rw [hcm']; ring
    simp_rw [hQ']
    rw [feynman _ _ hm1 hm2, ← heq, div_self (by positivity), sub_self, Real.sqrt_zero,
      photonKernel, if_pos rfl, hcm']
    field_simp
    ring

theorem closed_form_ph {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (p : ι → Vec3) (e η : ι → ℝ)
    (hm : ∀ n, 0 < m n) :
    photonIndex m p e η =
      -(1 / (8 * Real.pi ^ 2)) *
        ∑ n, ∑ k, η n * η k * e n * e k * photonKernel (relVel (m n) (p n) (m k) (p k)) := by
  have hE : ∀ n (u : Metric.sphere (0:Vec3) 1), 0 < energy (m n) (p n) - inner ℝ (p n) (u:Vec3) := by
    intro n u
    have h1 : ‖p n‖ < energy (m n) (p n) :=
      (Real.lt_sqrt (norm_nonneg _)).2 (by nlinarith [hm n])
    have h2 := real_inner_le_norm (p n) (u:Vec3)
    rw [norm_eq_of_mem_sphere, mul_one] at h2
    linarith
  have hint : ∀ n k, Integrable (fun u : Metric.sphere (0:Vec3) 1 =>
      e n * e k * η n * η k * mdot (m n) (p n) (m k) (p k) /
        ((energy (m n) (p n) - inner ℝ (p n) (u:Vec3)) *
          (energy (m k) (p k) - inner ℝ (p k) (u:Vec3)))) (volume.toSphere) := by
    intro n k
    refine (Continuous.div continuous_const (by fun_prop)
      (fun u => (mul_pos (hE n u) (hE k u)).ne')).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hterm : ∀ n k, ∫ u : Metric.sphere (0:Vec3) 1,
      e n * e k * η n * η k * mdot (m n) (p n) (m k) (p k) /
        ((energy (m n) (p n) - inner ℝ (p n) (u:Vec3)) *
          (energy (m k) (p k) - inner ℝ (p k) (u:Vec3))) ∂(volume.toSphere) =
      e n * e k * η n * η k * (-(2 * π) * photonKernel (relVel (m n) (p n) (m k) (p k))) := by
    intro n k
    rw [← pair_closed_ph _ _ _ _ (hm n) (hm k), ← mul_assoc, ← integral_const_mul]
    congr 1
    funext u
    ring
  rw [photonIndex, solidAngleIntegral]
  simp only [photonAngular]
  rw [integral_const_mul, integral_finsetSum _ (fun n _ => integrable_finsetSum _
    (fun k _ => hint n k))]
  rw [Finset.sum_congr rfl (fun n _ => integral_finsetSum _ (fun k _ => hint n k))]
  simp only [hterm]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hπ : π ≠ 0 := Real.pi_pos.ne'
  field_simp
  ring

end WeinbergBuild

set_option maxHeartbeats 4000000 in
open Weinberg1965 in
theorem solution {ι : Type*} [Fintype ι]
    (m : ι → ℝ) (p : ι → Vec3) (e η : ι → ℝ)
    (hm : ∀ n, 0 < m n) (hη : ∀ n, η n = 1 ∨ η n = -1) :
    photonIndex m p e η =
      -(1 / (8 * Real.pi ^ 2)) *
        ∑ n, ∑ k, η n * η k * e n * e k * photonKernel (relVel (m n) (p n) (m k) (p k)) := by
  exact WeinbergBuild.closed_form_ph m p e η hm
