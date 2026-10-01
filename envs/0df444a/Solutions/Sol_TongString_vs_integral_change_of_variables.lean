-- Prove2me | solution 1 for TongString.vs_integral_change_of_variables
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T10:53:06.905331+00:00
-- url     : https://prove2.me/submissions/970b58c6-e912-4118-9caa-03bec1764ba7

import Mathlib

set_option autoImplicit false

open Complex MeasureTheory Set

namespace VSC

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


/-- the right-hand integrand -/
noncomputable def R (a b : ℂ) (α β : ℝ) : ℂ :=
  (α : ℂ) ^ (-a - b) * (β : ℂ) ^ (-a) * ((1 - β : ℝ) : ℂ) ^ (-b) *
    cexp (-((α : ℂ) * β * (1 - β)))

noncomputable def Cb (a b : ℂ) (β : ℝ) : ℂ := (β : ℂ) ^ (-a) * ((1 - β : ℝ) : ℂ) ^ (-b)

lemma R_eq (a b : ℂ) (α β : ℝ) :
    R a b α β = Cb a b β *
      ((α : ℂ) ^ ((1 - a - b) - 1) * cexp (-(((β * (1 - β) : ℝ) : ℂ) * α))) := by
  simp only [R, Cb]
  rw [show (1 - a - b) - 1 = -a - b by ring]
  push_cast
  ring_nf

lemma R_inner_alg (a b : ℂ) {β : ℝ} (h0 : 0 < β) (h1 : β < 1) :
    Cb a b β * (((β * (1 - β) : ℝ) : ℂ) ^ (-(1 - a - b))) = Bc a b β := by
  have h1' : 0 < 1 - β := by linarith
  have hp : 0 < β * (1 - β) := mul_pos h0 h1'
  simp only [Cb, Bc]
  rw [ofReal_cpow_eq_exp h0, ofReal_cpow_eq_exp h1', ofReal_cpow_eq_exp hp,
    ofReal_cpow_eq_exp h1', ofReal_cpow_eq_exp h0, Real.log_mul h0.ne' h1'.ne']
  simp only [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma R_inner (a b : ℂ) (hc : 0 < (1 - a - b).re) {β : ℝ} (h0 : 0 < β) (h1 : β < 1) :
    ∫ α in Ioi (0:ℝ), R a b α β = Gamma (1 - a - b) * Bc a b β := by
  have hp : 0 < β * (1 - β) := mul_pos h0 (by linarith)
  simp_rw [R_eq]
  rw [integral_const_mul, gamma_rep hc hp, ← mul_assoc, R_inner_alg a b h0 h1]
  ring

lemma R_int {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re) (hc : 0 < (1 - a - b).re) :
    Integrable (fun q : ℝ × ℝ => R a b q.1 q.2)
      ((volume.restrict (Ioi (0:ℝ))).prod (volume.restrict (Ioo (0:ℝ) 1))) := by
  have hmeas : Measurable (fun q : ℝ × ℝ => R a b q.1 q.2) := by
    unfold R; fun_prop
  rw [integrable_prod_iff' hmeas.aestronglyMeasurable]
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with β hβ
    have hp : 0 < β * (1 - β) := mul_pos hβ.1 (by linarith [hβ.2])
    simp_rw [R_eq]
    exact (gamma_integrable hc hp).const_mul _
  · have hB := ((Bc_integrable ha hb).norm.const_mul (Real.Gamma (1 - a - b).re))
    refine hB.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with β hβ
    have h0 := hβ.1
    have h1 := hβ.2
    have hp : 0 < β * (1 - β) := mul_pos h0 (by linarith)
    have hn := congrArg norm (R_inner_alg a b h0 h1)
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hp] at hn
    simp only [R_eq, norm_mul]
    rw [integral_const_mul]
    have e : ∫ α in Ioi (0:ℝ), ‖(α : ℂ) ^ (1 - a - b - 1)‖ *
        ‖cexp (-(((β * (1 - β) : ℝ) : ℂ) * α))‖
        = ∫ α in Ioi (0:ℝ), α ^ ((1 - a - b).re - 1) * Real.exp (-((β * (1 - β)) * α)) := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun α hα => ?_)
      simp only [mem_Ioi] at hα
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hα, ← Complex.ofReal_mul, ← Complex.ofReal_neg,
        Complex.norm_exp_ofReal, show (1 - a - b - 1).re = (1 - a - b).re - 1 by simp]
    rw [e, Real.integral_rpow_mul_exp_neg_mul_Ioi hc hp]
    have e2 : (1 / (β * (1 - β))) ^ (1 - a - b).re = (β * (1 - β)) ^ (-(1 - a - b)).re := by
      rw [Complex.neg_re, Real.rpow_neg hp.le, one_div, Real.inv_rpow hp.le]
    rw [e2]
    linear_combination -(Real.Gamma (1 - a - b).re) * hn

lemma lhs_pt (a b : ℂ) (t u : ℝ) :
    (t : ℂ) ^ (-a) * (u : ℂ) ^ (-b) / ((t : ℂ) + u) * cexp (-((t : ℂ) * u / (t + u))) =
      (Real.pi : ℂ)⁻¹ * H a b (t, u) := by
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp only [H, gs]
  rw [show (1 - a) - 1 = -a by ring, show (1 - b) - 1 = -b by ring]
  push_cast
  rw [div_eq_mul_inv, div_eq_mul_inv (Real.pi : ℂ)]
  have : (Real.pi : ℂ)⁻¹ * Real.pi = 1 := inv_mul_cancel₀ hπ
  linear_combination (-((t : ℂ) ^ (-a) * (u : ℂ) ^ (-b) * ((t : ℂ) + u)⁻¹ *
    cexp (-((t : ℂ) * u / ((t : ℂ) + u))))) * this

end VSC

open Complex MeasureTheory in
theorem solution (a b : ℂ) (ha : 0 < a.re) (hb : 0 < b.re)
    (hab : (a + b).re < 1) :
    (∫ t in Set.Ioi (0 : ℝ), ∫ u in Set.Ioi (0 : ℝ),
        (t : ℂ) ^ (-a) * (u : ℂ) ^ (-b) / ((t : ℂ) + u) *
          Complex.exp (-((t : ℂ) * u / (t + u)))) =
      ∫ α in Set.Ioi (0 : ℝ), ∫ β in Set.Ioo (0 : ℝ) 1,
        (α : ℂ) ^ (-a - b) * (β : ℂ) ^ (-a) * ((1 - β : ℝ) : ℂ) ^ (-b) *
          Complex.exp (-((α : ℂ) * β * (1 - β))) := by
  have hc : 0 < (1 - a - b).re := by
    simp only [Complex.add_re] at hab
    simp only [Complex.sub_re, Complex.one_re]; linarith
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have eL : (∫ t in Set.Ioi (0 : ℝ), ∫ u in Set.Ioi (0 : ℝ),
        (t : ℂ) ^ (-a) * (u : ℂ) ^ (-b) / ((t : ℂ) + u) *
          Complex.exp (-((t : ℂ) * u / (t + u)))) =
      (Real.pi : ℂ)⁻¹ * ∫ t in Set.Ioi (0 : ℝ), ∫ u in Set.Ioi (0 : ℝ), VSC.H a b (t, u) := by
    rw [← integral_const_mul]
    congr 1; funext t
    rw [← integral_const_mul]
    congr 1; funext u
    exact VSC.lhs_pt a b t u
  have eR : (∫ α in Set.Ioi (0 : ℝ), ∫ β in Set.Ioo (0 : ℝ) 1,
        (α : ℂ) ^ (-a - b) * (β : ℂ) ^ (-a) * ((1 - β : ℝ) : ℂ) ^ (-b) *
          Complex.exp (-((α : ℂ) * β * (1 - β)))) =
      ∫ α in Set.Ioi (0 : ℝ), ∫ β in Set.Ioo (0 : ℝ) 1, VSC.R a b α β := rfl
  rw [eL, eR, ← integral_prod _ (VSC.H_int ha hb hc), VSC.H_value ha hb hc,
    integral_integral_swap (f := fun α β => VSC.R a b α β) (VSC.R_int ha hb hc)]
  have e3 : ∫ β in Set.Ioo (0 : ℝ) 1, ∫ α in Set.Ioi (0 : ℝ), VSC.R a b α β =
      ∫ β in Set.Ioo (0 : ℝ) 1, Gamma (1 - a - b) * VSC.Bc a b β :=
    setIntegral_congr_fun measurableSet_Ioo (fun β hβ => VSC.R_inner a b hc hβ.1 hβ.2)
  rw [e3, integral_const_mul]
  field_simp
