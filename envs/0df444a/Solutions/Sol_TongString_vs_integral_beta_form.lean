-- Prove2me | solution 1 for TongString.vs_integral_beta_form
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-30T16:05:14.618092+00:00
-- url     : https://prove2.me/submissions/7eed500a-3f25-4d79-adcf-8ed228f458b3

import Mathlib
import Definitions.Def_TongString_vs_integral

set_option autoImplicit false

open Complex MeasureTheory Set

namespace VSP

lemma ofReal_cpow_eq_exp {x : ℝ} (hx : 0 < x) (w : ℂ) :
    (x : ℂ) ^ w = cexp (Real.log x * w) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hx.ne'), ← Complex.ofReal_log hx.le]

lemma gamma_rep {s : ℂ} (hs : 0 < s.re) {r : ℝ} (hr : 0 < r) :
    ∫ t in Ioi (0:ℝ), (t:ℂ) ^ (s - 1) * cexp (-((r:ℂ) * t)) = (r:ℂ) ^ (-s) * Gamma s := by
  rw [Complex.integral_cpow_mul_exp_neg_mul_Ioi hs hr]
  congr 1
  have : (1 / (r:ℂ)) = ((r⁻¹ : ℝ) : ℂ) := by push_cast; ring
  rw [this, ofReal_cpow_eq_exp (inv_pos.mpr hr), ofReal_cpow_eq_exp hr, Real.log_inv]
  congr 1; push_cast; ring_nf

lemma gamma_integrable {s : ℂ} (hs : 0 < s.re) {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => (t:ℂ) ^ (s - 1) * cexp (-((r:ℂ) * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (s := s.re - 1) (p := 1) (b := r)
    (by linarith) one_pos hr
  refine h.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    intro t ht
    refine ContinuousAt.continuousWithinAt ?_
    refine ContinuousAt.mul ?_ (by fun_prop)
    exact (continuousAt_ofReal_cpow_const _ _ (Or.inr (ne_of_gt ht)))
  · refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_exp, Real.rpow_one]
    simp

lemma gauss (t u : ℝ) (ht : 0 < t) (hu : 0 < u) :
    ∫ z : ℂ, cexp (-(((‖z‖ ^ 2 : ℝ) : ℂ) * t)) * cexp (-(((‖1 - z‖ ^ 2 : ℝ) : ℂ) * u)) =
      (Real.pi / (t + u) : ℂ) * cexp (-((t * u / (t + u) : ℝ) : ℂ)) := by
  have hb : 0 < ((t + u : ℝ) : ℂ).re := by simp; linarith
  have key := GaussianFourier.integral_cexp_neg_mul_sq_norm_add (V := ℂ) hb (2 * u) 1
  have e : ∀ z : ℂ, cexp (-(((‖z‖ ^ 2 : ℝ) : ℂ) * t)) * cexp (-(((‖1 - z‖ ^ 2 : ℝ) : ℂ) * u)) =
      cexp (-((t + u : ℝ) : ℂ) * ‖z‖ ^ 2 + (2 * u) * ((inner ℝ (1 : ℂ) z : ℝ) : ℂ)) * cexp (-u) := by
    intro z
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    have h1 : ‖1 - z‖ ^ 2 = 1 - 2 * z.re + ‖z‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      simp; ring_nf
    have h2 : inner ℝ (1 : ℂ) z = z.re := by simp [Complex.inner]
    rw [h1, h2]; push_cast; ring_nf
  simp_rw [e]
  rw [integral_mul_const, key]
  rw [Complex.finrank_real_complex]
  have hne' : (t : ℂ) + u ≠ 0 := by exact_mod_cast (by linarith : t + u ≠ 0)
  have hp : (((Real.pi : ℂ) / ((t + u : ℝ) : ℂ)) ^ (((2 : ℕ) : ℂ) / 2)) = (Real.pi / (t + u) : ℂ) := by
    norm_num
  rw [hp, mul_assoc, ← Complex.exp_add]
  congr 2
  simp only [norm_one, ofReal_one, one_pow, mul_one]
  push_cast
  field_simp
  ring_nf


lemma ofReal_eq_exp_log {y : ℝ} (hy : 0 < y) : (y : ℂ) = cexp (Real.log y) := by
  rw [← Complex.ofReal_exp, Real.exp_log hy]

lemma ofReal_inv_eq_exp_log {y : ℝ} (hy : 0 < y) : ((y : ℂ))⁻¹ = cexp (-(Real.log y : ℂ)) := by
  rw [ofReal_eq_exp_log hy, ← Complex.exp_neg]

/-- the Beta integrand, as in the target -/
noncomputable def Bc (a b : ℂ) (β : ℝ) : ℂ := ((1 - β : ℝ) : ℂ) ^ (a - 1) * (β : ℂ) ^ (b - 1)

noncomputable def K (a b : ℂ) (x : ℝ) : ℂ := |1 / (1 + x) ^ 2| • Bc a b (x / (1 + x))

lemma subst_image : (fun x : ℝ => x / (1 + x)) '' Ioi 0 = Ioo 0 1 := by
  ext y
  simp only [mem_image, mem_Ioi, mem_Ioo]
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨by positivity, ?_⟩
    rw [div_lt_one (by linarith)]; linarith
  · rintro ⟨h0, h1⟩
    refine ⟨y / (1 - y), div_pos h0 (by linarith), ?_⟩
    have : (1 - y) ≠ 0 := by linarith
    field_simp
    ring

lemma subst_deriv (x : ℝ) (hx : x ∈ Ioi (0:ℝ)) :
    HasDerivWithinAt (fun x : ℝ => x / (1 + x)) (1 / (1 + x) ^ 2) (Ioi 0) x := by
  have hx' : (1 + x) ≠ 0 := by simp only [mem_Ioi] at hx; linarith
  have h := (hasDerivAt_id' x).div ((hasDerivAt_id' x).const_add 1) hx'
  have e : (1 * (1 + x) - x * 1) / (1 + x) ^ 2 = 1 / (1 + x) ^ 2 := by ring
  rw [e] at h
  exact h.hasDerivWithinAt

lemma subst_inj : InjOn (fun x : ℝ => x / (1 + x)) (Ioi 0) := by
  intro x hx y hy hxy
  simp only [mem_Ioi] at hx hy
  have h1 : (1 + x) ≠ 0 := by linarith
  have h2 : (1 + y) ≠ 0 := by linarith
  simp only at hxy
  rw [div_eq_div_iff h1 h2] at hxy
  linarith

lemma Bc_integrable {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    IntegrableOn (Bc a b) (Ioo 0 1) := by
  have h := (Complex.betaIntegral_convergent hb ha)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at h
  refine (h.mono_set Ioo_subset_Ioc_self).congr_fun (fun β _ => ?_) measurableSet_Ioo
  simp only [Bc]; push_cast; ring_nf

lemma K_integrable {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) :
    IntegrableOn (K a b) (Ioi 0) := by
  have := (integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi subst_deriv
    subst_inj (Bc a b)).mp (by rw [subst_image]; exact Bc_integrable ha hb)
  exact this

lemma K_integral (a b : ℂ) :
    ∫ x in Ioi (0:ℝ), K a b x = ∫ β in Ioo (0:ℝ) 1, Bc a b β := by
  rw [← subst_image, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi subst_deriv
    subst_inj (Bc a b)]
  rfl

/-- the (x,u) integrand after substituting t = u x -/
noncomputable def L (a b : ℂ) (x u : ℝ) : ℂ :=
  ((Real.pi : ℂ) * (x : ℂ) ^ (-a) * ((1 + x : ℝ) : ℂ)⁻¹) *
    ((u : ℂ) ^ ((1 - a - b) - 1) * cexp (-(((x / (1 + x) : ℝ) : ℂ) * u)))

lemma L_inner_alg (a b : ℂ) {x : ℝ} (hx : 0 < x) :
    ((Real.pi : ℂ) * (x : ℂ) ^ (-a) * ((1 + x : ℝ) : ℂ)⁻¹) *
      (((x / (1 + x) : ℝ) : ℂ) ^ (-(1 - a - b))) = (Real.pi : ℂ) * K a b x := by
  have h1 : 0 < 1 + x := by linarith
  have hl : x / (1 + x) > 0 := by positivity
  simp only [K, Bc, Complex.real_smul]
  rw [abs_of_pos (by positivity)]
  have e1 : 1 - x / (1 + x) = (1 + x)⁻¹ := by field_simp; ring
  rw [e1, ofReal_cpow_eq_exp hx, ofReal_cpow_eq_exp hl, ofReal_cpow_eq_exp (inv_pos.mpr h1),
    ofReal_cpow_eq_exp hl, ofReal_inv_eq_exp_log h1, Real.log_div hx.ne' h1.ne', Real.log_inv]
  have e2 : ((1 / (1 + x) ^ 2 : ℝ) : ℂ) = cexp (-2 * (Real.log (1 + x) : ℂ)) := by
    rw [show (1 / (1 + x) ^ 2 : ℝ) = ((1 + x) ^ 2)⁻¹ by ring, Complex.ofReal_inv,
      ofReal_inv_eq_exp_log (by positivity), Real.log_pow]
    push_cast; ring_nf
  rw [e2]
  simp only [mul_assoc, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

lemma L_inner (a b : ℂ) (hc : 0 < (1 - a - b).re) {x : ℝ} (hx : 0 < x) :
    ∫ u in Ioi (0:ℝ), L a b x u = (Real.pi : ℂ) * Gamma (1 - a - b) * K a b x := by
  have hl : x / (1 + x) > 0 := by positivity
  simp only [L]
  rw [integral_const_mul, gamma_rep hc hl, ← mul_assoc, L_inner_alg a b hx]
  ring


noncomputable def gs (t u : ℝ) : ℂ := (Real.pi / (t + u) : ℂ) * cexp (-((t * u / (t + u) : ℝ) : ℂ))

noncomputable def H (a b : ℂ) (p : ℝ × ℝ) : ℂ :=
  (p.1 : ℂ) ^ ((1 - a) - 1) * (p.2 : ℂ) ^ ((1 - b) - 1) * gs p.1 p.2

lemma subst_pt (a b : ℂ) {x u : ℝ} (hx : 0 < x) (hu : 0 < u) :
    (u : ℂ) * H a b (u * x, u) = L a b x u := by
  have h1 : 0 < 1 + x := by linarith
  have hux : 0 < u * x := by positivity
  simp only [H, gs, L]
  have harg : (((u * x) * u / (u * x + u) : ℝ) : ℂ) = ((x / (1 + x) : ℝ) : ℂ) * u := by
    rw [← Complex.ofReal_mul]; congr 1; field_simp; ring
  have hden : (Real.pi / (((u * x : ℝ) : ℂ) + u) : ℂ) =
      Real.pi * cexp (-(Real.log u : ℂ)) * cexp (-(Real.log (1 + x) : ℂ)) := by
    rw [← ofReal_inv_eq_exp_log hu, ← ofReal_inv_eq_exp_log h1]
    have : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
    have : ((1 + x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h1.ne'
    push_cast
    field_simp
    ring
  rw [harg, hden, ofReal_cpow_eq_exp hux, ofReal_cpow_eq_exp hu, ofReal_cpow_eq_exp hx,
    ofReal_cpow_eq_exp hu, ofReal_inv_eq_exp_log h1, Real.log_mul hu.ne' hx.ne']
  have key : (u : ℂ) * cexp (↑(Real.log u + Real.log x) * (1 - a - 1)) *
      cexp (↑(Real.log u) * (1 - b - 1)) * cexp (-↑(Real.log u)) * cexp (-↑(Real.log (1 + x))) =
      cexp (↑(Real.log x) * -a) * cexp (-↑(Real.log (1 + x))) *
        cexp (↑(Real.log u) * (1 - a - b - 1)) := by
    rw [ofReal_eq_exp_log hu]
    simp only [← Complex.exp_add]
    congr 1
    push_cast
    ring
  linear_combination (Real.pi : ℂ) * cexp (-(((x / (1 + x) : ℝ) : ℂ) * u)) * key

lemma L_int {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < (1 - a - b).re) :
    Integrable (fun q : ℝ × ℝ => L a b q.1 q.2)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
  have hmeas : Measurable (fun q : ℝ × ℝ => L a b q.1 q.2) := by
    unfold L; fun_prop
  rw [integrable_prod_iff hmeas.aestronglyMeasurable]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hl : x / (1 + x) > 0 := by simp only [mem_Ioi] at hx; positivity
    exact (gamma_integrable hc hl).const_mul _
  · have hK := ((K_integrable ha hb).norm.const_mul
      (Real.Gamma (1 - a - b).re * Real.pi))
    refine hK.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simp only [mem_Ioi] at hx
    have h1 : 0 < 1 + x := by linarith
    have hl : 0 < x / (1 + x) := by positivity
    have hn := congrArg norm (L_inner_alg a b hx)
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hl] at hn
    simp only [L, norm_mul]
    rw [integral_const_mul]
    have e : ∫ u in Ioi (0:ℝ), ‖(u : ℂ) ^ (1 - a - b - 1)‖ * ‖cexp (-(((x / (1 + x) : ℝ) : ℂ) * u))‖
        = ∫ u in Ioi (0:ℝ), u ^ ((1 - a - b).re - 1) * Real.exp (-((x / (1 + x)) * u)) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
      simp only [mem_Ioi] at hu
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hu, ← Complex.ofReal_mul, ← Complex.ofReal_neg,
        Complex.norm_exp_ofReal, show (1 - a - b - 1).re = (1 - a - b).re - 1 by simp]
    rw [e, Real.integral_rpow_mul_exp_neg_mul_Ioi hc hl]
    have e2 : (1 / (x / (1 + x))) ^ (1 - a - b).re = (x / (1 + x)) ^ (-(1 - a - b)).re := by
      rw [Complex.neg_re, Real.rpow_neg hl.le, one_div, Real.inv_rpow hl.le]
    rw [e2]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos] at hn ⊢
    linear_combination -(Real.Gamma (1 - a - b).re) * hn


lemma H_inner_subst (a b : ℂ) {u : ℝ} (hu : 0 < u) :
    ∫ t in Ioi (0:ℝ), H a b (t, u) = ∫ x in Ioi (0:ℝ), L a b x u := by
  calc ∫ t in Ioi (0:ℝ), H a b (t, u) = ∫ t in Ioi (u * 0), H a b (t, u) := by rw [mul_zero]
    _ = u • ∫ x in Ioi (0:ℝ), H a b (u * x, u) :=
        (integral_comp_mul_left_Ioi' (fun t => H a b (t, u)) 0 hu).symm
    _ = ∫ x in Ioi (0:ℝ), (u : ℂ) * H a b (u * x, u) := by
        rw [Complex.real_smul, integral_const_mul]
    _ = ∫ x in Ioi (0:ℝ), L a b x u :=
        setIntegral_congr_fun measurableSet_Ioi (fun x hx => subst_pt a b hx hu)

lemma H_norm_subst (a b : ℂ) {u : ℝ} (hu : 0 < u) :
    ∫ t in Ioi (0:ℝ), ‖H a b (t, u)‖ = ∫ x in Ioi (0:ℝ), ‖L a b x u‖ := by
  calc ∫ t in Ioi (0:ℝ), ‖H a b (t, u)‖ = ∫ t in Ioi (u * 0), ‖H a b (t, u)‖ := by rw [mul_zero]
    _ = u • ∫ x in Ioi (0:ℝ), ‖H a b (u * x, u)‖ :=
        (integral_comp_mul_left_Ioi' (fun t => ‖H a b (t, u)‖) 0 hu).symm
    _ = ∫ x in Ioi (0:ℝ), ‖(u : ℂ) * H a b (u * x, u)‖ := by
        rw [smul_eq_mul, ← integral_const_mul]
        congr 1; ext x
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
    _ = ∫ x in Ioi (0:ℝ), ‖L a b x u‖ :=
        setIntegral_congr_fun measurableSet_Ioi (fun x hx => by rw [subst_pt a b hx hu])

lemma H_int {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < (1 - a - b).re) :
    Integrable (H a b) ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) := by
  have hL := L_int ha hb hc
  have hmeas : Measurable (H a b) := by
    unfold H gs; fun_prop
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  constructor
  · filter_upwards [hL.prod_left_ae, ae_restrict_mem measurableSet_Ioi] with u hLu hu
    simp only [mem_Ioi] at hu
    have h2 : IntegrableOn (fun x => H a b (u * x, u)) (Ioi 0) := by
      refine (show IntegrableOn (fun x => (u : ℂ)⁻¹ * L a b x u) (Ioi 0) volume from
        hLu.const_mul _).congr_fun (fun x hx => ?_) measurableSet_Ioi
      simp only [mem_Ioi] at hx
      have hu' : (u : ℂ) ≠ 0 := by exact_mod_cast hu.ne'
      simp only
      rw [← subst_pt a b hx hu]
      field_simp
    have := (integrableOn_Ioi_comp_mul_left_iff (fun t => H a b (t, u)) 0 hu).mp h2
    rw [mul_zero] at this
    exact this
  · refine hL.integral_norm_prod_right.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact (H_norm_subst a b hu).symm

lemma H_value {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < (1 - a - b).re) :
    ∫ p, H a b p ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))) =
      (Real.pi : ℂ) * Gamma (1 - a - b) * ∫ β in Ioo (0:ℝ) 1, Bc a b β := by
  have hL := L_int ha hb hc
  rw [integral_prod_symm _ (H_int ha hb hc)]
  have e1 : ∫ u in Ioi (0:ℝ), ∫ t in Ioi (0:ℝ), H a b (t, u) =
      ∫ u in Ioi (0:ℝ), ∫ x in Ioi (0:ℝ), L a b x u := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun u hu => ?_)
    exact H_inner_subst a b hu
  rw [e1]
  have e2 := integral_integral_swap (f := fun x u => L a b x u) (μ := volume.restrict (Ioi (0:ℝ)))
    (ν := volume.restrict (Ioi (0:ℝ))) hL
  rw [← e2]
  have e3 : ∫ x in Ioi (0:ℝ), ∫ u in Ioi (0:ℝ), L a b x u =
      ∫ x in Ioi (0:ℝ), (Real.pi : ℂ) * Gamma (1 - a - b) * K a b x := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    exact L_inner a b hc hx
  rw [e3, integral_const_mul, K_integral]


lemma gauss_pt (t u : ℝ) (z : ℂ) :
    cexp (-(((‖z‖ ^ 2 : ℝ) : ℂ) * t)) * cexp (-(((‖1 - z‖ ^ 2 : ℝ) : ℂ) * u)) =
      cexp (-((t + u : ℝ) : ℂ) * ‖z‖ ^ 2 + (2 * u) * ((inner ℝ (1 : ℂ) z : ℝ) : ℂ)) * cexp (-u) := by
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have h1 : ‖1 - z‖ ^ 2 = 1 - 2 * z.re + ‖z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp; ring
  have h2 : inner ℝ (1 : ℂ) z = z.re := by simp [Complex.inner]
  rw [h1, h2]; push_cast; ring

lemma gauss_integrable (t u : ℝ) (ht : 0 < t) (hu : 0 < u) :
    Integrable (fun z : ℂ => cexp (-(((‖z‖ ^ 2 : ℝ) : ℂ) * t)) *
      cexp (-(((‖1 - z‖ ^ 2 : ℝ) : ℂ) * u))) := by
  have hb : 0 < ((t + u : ℝ) : ℂ).re := by simp; linarith
  have := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := ℂ) hb (2 * u) 1).mul_const
    (cexp (-u))
  exact this.congr (Filter.Eventually.of_forall fun z => (gauss_pt t u z).symm)

lemma gauss_norm (t u : ℝ) (ht : 0 < t) (hu : 0 < u) :
    ∫ z : ℂ, ‖cexp (-(((‖z‖ ^ 2 : ℝ) : ℂ) * t)) * cexp (-(((‖1 - z‖ ^ 2 : ℝ) : ℂ) * u))‖ =
      ‖gs t u‖ := by
  have hpt : ∀ z : ℂ, cexp (-(((‖z‖ ^ 2 : ℝ) : ℂ) * t)) * cexp (-(((‖1 - z‖ ^ 2 : ℝ) : ℂ) * u)) =
      ((Real.exp (-(‖z‖ ^ 2 * t)) * Real.exp (-(‖1 - z‖ ^ 2 * u)) : ℝ) : ℂ) := by
    intro z; push_cast; ring_nf
  have hg : gs t u = ∫ z : ℂ, cexp (-(((‖z‖ ^ 2 : ℝ) : ℂ) * t)) *
      cexp (-(((‖1 - z‖ ^ 2 : ℝ) : ℂ) * u)) := (gauss t u ht hu).symm
  rw [hg]
  simp_rw [hpt]
  rw [integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (integral_nonneg (fun z => by positivity))]
  congr 1; ext z
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]

noncomputable def F (a : ℂ) (z : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ ((1 - a) - 1) * cexp (-(((‖z‖ ^ 2 : ℝ) : ℂ) * t))

noncomputable def G (a b : ℂ) (z : ℂ) (p : ℝ × ℝ) : ℂ := F a z p.1 * F b (1 - z) p.2

lemma G_eq (a b z : ℂ) (p : ℝ × ℝ) : G a b z p =
    ((p.1 : ℂ) ^ ((1 - a) - 1) * (p.2 : ℂ) ^ ((1 - b) - 1)) *
      (cexp (-(((‖z‖ ^ 2 : ℝ) : ℂ) * p.1)) * cexp (-(((‖1 - z‖ ^ 2 : ℝ) : ℂ) * p.2))) := by
  simp only [G, F]; ring

lemma pos_ae : ∀ᵐ p ∂((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ)))),
    0 < p.1 ∧ 0 < p.2 := by
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioi)] with p hp
  exact ⟨hp.1, hp.2⟩

lemma G_inner (a b : ℂ) (p : ℝ × ℝ) (hp : 0 < p.1 ∧ 0 < p.2) :
    ∫ z, G a b z p = H a b p := by
  simp_rw [G_eq]
  rw [integral_const_mul, gauss p.1 p.2 hp.1 hp.2]
  rfl

lemma G_int {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < (1 - a - b).re) :
    Integrable (fun q : ℂ × (ℝ × ℝ) => G a b q.1 q.2)
      ((volume : Measure ℂ).prod
        ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioi (0:ℝ))))) := by
  have hmeas : Measurable (fun q : ℂ × (ℝ × ℝ) => G a b q.1 q.2) := by
    unfold G F; fun_prop
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  constructor
  · filter_upwards [pos_ae] with p hp
    simp_rw [G_eq]
    exact (gauss_integrable p.1 p.2 hp.1 hp.2).const_mul _
  · refine (H_int ha hb hc).norm.congr ?_
    filter_upwards [pos_ae] with p hp
    simp_rw [G_eq, norm_mul]
    rw [integral_const_mul]
    have := gauss_norm p.1 p.2 hp.1 hp.2
    simp only [norm_mul] at this
    rw [this]
    simp only [H, norm_mul]

lemma pow2 {r : ℝ} (hr : 0 < r) (a : ℂ) :
    ((r ^ 2 : ℝ) : ℂ) ^ (-(1 - a)) = (r : ℂ) ^ (2 * a - 2) := by
  rw [ofReal_cpow_eq_exp (by positivity), ofReal_cpow_eq_exp hr, Real.log_pow]
  congr 1; push_cast; ring

lemma rep_z {a : ℂ} (ha : 0 < (1 - a).re) {w : ℂ} (hw : w ≠ 0) :
    ∫ t in Ioi (0:ℝ), F a w t = (‖w‖ : ℂ) ^ (2 * a - 2) * Gamma (1 - a) := by
  have hr : 0 < ‖w‖ ^ 2 := by positivity
  simp only [F]
  rw [gamma_rep ha hr, pow2 (norm_pos_iff.mpr hw)]

end VSP

open Complex MeasureTheory TongString in
theorem solution (a b c : ℂ) (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < c.re)
    (habc : a + b + c = 1) :
    virasoroShapiroIntegral a b =
      2 * Real.pi * Gamma c / (Gamma (1 - a) * Gamma (1 - b)) *
        ∫ β in Set.Ioo (0 : ℝ) 1, ((1 - β : ℝ) : ℂ) ^ (a - 1) * (β : ℂ) ^ (b - 1) := by
  have hc' : c = 1 - a - b := by linear_combination habc
  subst hc'
  have hre : 0 < 1 - a.re - b.re := by simpa using hc
  have ha1 : 0 < (1 - a).re := by simp; linarith
  have hb1 : 0 < (1 - b).re := by simp; linarith
  have hΓa : Gamma (1 - a) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos ha1
  have hΓb : Gamma (1 - b) ≠ 0 := Complex.Gamma_ne_zero_of_re_pos hb1
  have hG := VSP.G_int ha hb hc
  have h0 : ∀ᵐ z : ℂ, z ≠ 0 := by
    simp [ae_iff, measure_singleton]
  have h1 : ∀ᵐ z : ℂ, z ≠ 1 := by
    simp [ae_iff, measure_singleton]
  have step1 : ∀ᵐ z : ℂ, ((‖z‖ : ℂ) ^ (2 * a - 2)) * ((‖1 - z‖ : ℂ) ^ (2 * b - 2)) =
      (Gamma (1 - a) * Gamma (1 - b))⁻¹ *
        ∫ p, VSP.G a b z p ∂((volume.restrict (Set.Ioi (0:ℝ))).prod
          (volume.restrict (Set.Ioi (0:ℝ)))) := by
    filter_upwards [h0, h1] with z hz0 hz1
    rw [show (∫ p, VSP.G a b z p ∂((volume.restrict (Set.Ioi (0:ℝ))).prod
          (volume.restrict (Set.Ioi (0:ℝ))))) =
        (∫ t in Set.Ioi (0:ℝ), VSP.F a z t) * (∫ u in Set.Ioi (0:ℝ), VSP.F b (1 - z) u) from
      integral_prod_mul (VSP.F a z) (VSP.F b (1 - z))]
    rw [VSP.rep_z ha1 hz0, VSP.rep_z hb1 (sub_ne_zero.mpr hz1.symm)]
    field_simp
  have step2 : ∀ᵐ p ∂((volume.restrict (Set.Ioi (0:ℝ))).prod (volume.restrict (Set.Ioi (0:ℝ)))),
      ∫ z, VSP.G a b z p = VSP.H a b p := by
    filter_upwards [VSP.pos_ae] with p hp
    exact VSP.G_inner a b p hp
  unfold virasoroShapiroIntegral
  rw [integral_congr_ae step1, integral_const_mul,
    integral_integral_swap (f := fun z p => VSP.G a b z p) hG, integral_congr_ae step2,
    VSP.H_value ha hb hc]
  simp only [VSP.Bc]
  field_simp
