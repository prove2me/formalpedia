-- Prove2me | solution 1 for WangGreenTech.Regulation.proposition_3a
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T06:04:02.317926+00:00
-- url     : https://prove2.me/submissions/348a23dc-458a-406c-bbfa-ec36bec968b3

import Mathlib
import Definitions.Def_WangGreenTech_Regulation_Policies

set_option autoImplicit false

open WangGreenTech.Regulation MeasureTheory Set

lemma s226w_int (p : Model) (hε : 0 < p.ε) (f : ℝ → ℝ) (x : ℝ) :
    ∫ θ, f θ ∂posterior p x = (2*p.ε)⁻¹ * ∫ θ in (x-p.ε)..(x+p.ε), f θ := by
  unfold posterior
  rw [integral_smul_measure, intervalIntegral.integral_of_le (by linarith),
    ← integral_Icc_eq_integral_Ioc, ENNReal.toReal_inv, ENNReal.toReal_ofReal (by linarith),
    smul_eq_mul]

lemma s226w_intg (p : Model) (hε : 0 < p.ε) {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    Integrable f (posterior p x) := by
  unfold posterior
  exact (hf.integrableOn_Icc).smul_measure
    (ENNReal.inv_ne_top.2 (by rw [Ne, ENNReal.ofReal_eq_zero]; exact not_le.2 (by linarith)))

lemma s226w_tm (p : Model) (hε : 0 < p.ε) (t θ : ℝ) :
    thresholdMass p t θ = (max 0 (θ - (t - p.ε)) - max 0 (θ - (t + p.ε)))/(2*p.ε) := by
  unfold thresholdMass
  rcases le_total (θ - (t - p.ε)) 0 with h1 | h1
  · have : (θ + p.ε - t)/(2*p.ε) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
    rw [max_eq_left this, min_eq_right zero_le_one, max_eq_left h1, max_eq_left (by linarith)]
    simp
  rcases le_total (θ - (t + p.ε)) 0 with h2 | h2
  · have h3 : 0 ≤ (θ + p.ε - t)/(2*p.ε) := div_nonneg (by linarith) (by linarith)
    have h4 : (θ + p.ε - t)/(2*p.ε) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    rw [max_eq_right h3, min_eq_right h4, max_eq_right h1, max_eq_left h2]; congr 1; ring
  · have h4 : 1 ≤ (θ + p.ε - t)/(2*p.ε) := by rw [le_div_iff₀ (by linarith)]; linarith
    rw [max_eq_right (by linarith), min_eq_left h4, max_eq_right h1, max_eq_right h2,
      eq_div_iff (by linarith)]; ring

lemma s226w_tmc (p : Model) (t : ℝ) : Continuous (thresholdMass p t) := by
  show Continuous (fun θ => min 1 (max 0 ((θ + p.ε - t) / (2 * p.ε)))); fun_prop

lemma s226w_mass (p : Model) (hε : 0 < p.ε) (t θ : ℝ) :
    adoptionMass p (thresholdProfile t) θ = thresholdMass p t θ := by
  have hin : ∫ x, (if t ≤ x then (1:ℝ) else 0) ∂signalLaw p θ = thresholdMass p t θ := by
    rw [show (fun x : ℝ => if t ≤ x then (1:ℝ) else 0) = (Ici t).indicator 1 from by
      ext x; simp [indicator]]
    rw [integral_indicator_one measurableSet_Ici, Measure.real]
    unfold signalLaw posterior
    have hI : Ici t ∩ Icc (θ - p.ε) (θ + p.ε) = Icc (max t (θ - p.ε)) (θ + p.ε) := by
      ext z; simp only [mem_inter_iff, mem_Ici, mem_Icc, max_le_iff]; tauto
    rw [Measure.smul_apply, Measure.restrict_apply measurableSet_Ici, hI, Real.volume_Icc,
      smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal (by linarith),
      ENNReal.toReal_ofReal', s226w_tm p hε, div_eq_inv_mul]
    congr 1
    rcases le_total t (θ - p.ε) with h1 | h1
    · rw [max_eq_right h1, max_eq_left (by linarith), max_eq_right (by linarith),
        max_eq_right (by linarith)]; ring
    rcases le_total t (θ + p.ε) with h2 | h2
    · rw [max_eq_left h1, max_eq_left (by linarith), max_eq_right (by linarith),
        max_eq_left (by linarith)]; ring
    · rw [max_eq_left h1, max_eq_right (by linarith), max_eq_left (by linarith),
        max_eq_left (by linarith)]; ring
  unfold adoptionMass thresholdProfile
  simp only [decide_eq_true_eq, hin]
  simp


noncomputable def s226w_cl (w : ℝ) : ℝ := min 1 (max 0 w)
noncomputable def s226w_f (b C r w : ℝ) : ℝ := -b * s226w_cl w + C * (s226w_cl w) ^ r
noncomputable def s226w_F (b C r y : ℝ) : ℝ := ∫ w in (0:ℝ)..y, s226w_f b C r w
noncomputable def s226w_Phi (e b C r v : ℝ) : ℝ :=
  2*e*v + s226w_F b C r (v+1) - s226w_F b C r v

lemma s226w_cl0 {w : ℝ} (h : w ≤ 0) : s226w_cl w = 0 := by
  unfold s226w_cl; rw [max_eq_left h]; simp
lemma s226w_clid {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 1) : s226w_cl w = w := by
  unfold s226w_cl; rw [max_eq_right h0, min_eq_right h1]
lemma s226w_cl1 {w : ℝ} (h : 1 ≤ w) : s226w_cl w = 1 := by
  unfold s226w_cl; rw [max_eq_right (by linarith), min_eq_left h]
lemma s226w_clc : Continuous s226w_cl := by unfold s226w_cl; fun_prop

lemma s226w_fc (b C : ℝ) {r : ℝ} (hr : 0 < r) : Continuous (s226w_f b C r) := by
  unfold s226w_f
  exact (continuous_const.mul s226w_clc).add
    (continuous_const.mul (s226w_clc.rpow_const (fun _ => Or.inr hr.le)))

lemma s226w_Fderiv (b C : ℝ) {r : ℝ} (hr : 0 < r) (y : ℝ) :
    HasDerivAt (s226w_F b C r) (s226w_f b C r y) y :=
  ((s226w_fc b C hr).integral_hasStrictDerivAt 0 y).hasDerivAt

lemma s226w_Phideriv (e b C : ℝ) {r : ℝ} (hr : 0 < r) (v : ℝ) :
    HasDerivAt (s226w_Phi e b C r) (2*e + s226w_f b C r (v+1) - s226w_f b C r v) v := by
  have h1 : HasDerivAt (fun x => s226w_F b C r (x + 1)) (s226w_f b C r (v+1)) v :=
    (s226w_Fderiv b C hr (v+1)).comp_add_const v 1
  have := ((((hasDerivAt_id' v).const_mul (2*e)).add h1).sub (s226w_Fderiv b C hr v))
  exact this.congr_deriv (by ring)

lemma s226w_F01 (b C : ℝ) {r : ℝ} (hr : 0 < r) :
    s226w_F b C r 1 - s226w_F b C r 0 = -b/2 + C/(r+1) := by
  unfold s226w_F
  rw [intervalIntegral.integral_same, sub_zero]
  have : ∫ w in (0:ℝ)..1, s226w_f b C r w = ∫ w in (0:ℝ)..1, (-b * w + C * w^r) :=
    intervalIntegral.integral_congr (fun w hw => by
      rw [uIcc_of_le zero_le_one] at hw; simp only [s226w_f, s226w_clid hw.1 hw.2])
  rw [this, intervalIntegral.integral_add (f := fun w => -b * w) (g := fun w => C * w^r)
      ((continuous_const.mul continuous_id).intervalIntegrable _ _)
      ((continuous_const.mul (continuous_id.rpow_const (fun _ => Or.inr hr.le))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, integral_id,
    integral_rpow (Or.inl (by linarith))]
  rw [Real.one_rpow, Real.zero_rpow (by linarith : r + 1 ≠ 0)]
  ring

lemma s226w_Phid_nonneg {e b C r : ℝ} (he : 0 < e) (hr : 0 < r)
    (h1 : ∀ u, 0 < u → u ≤ 1 → b*u ≤ 2*e + C*u^r)
    (h2 : ∀ s, 0 ≤ s → s < 1 → b*(1-s) ≤ 2*e + C*(1 - s^r)) (v : ℝ) :
    0 ≤ 2*e + s226w_f b C r (v+1) - s226w_f b C r v := by
  have z : (0:ℝ)^r = 0 := Real.zero_rpow hr.ne'
  unfold s226w_f
  rcases le_total v (-1) with hv | hv
  · rw [s226w_cl0 (by linarith : v+1 ≤ 0), s226w_cl0 (by linarith : v ≤ 0), z]; linarith
  rcases le_total v 0 with hv2 | hv2
  · rw [s226w_clid (by linarith) (by linarith : v+1 ≤ 1), s226w_cl0 hv2, z]
    rcases eq_or_lt_of_le hv with h | h
    · rw [← h]; norm_num [z]; linarith
    · have := h1 (v+1) (by linarith) (by linarith); nlinarith
  rcases le_total v 1 with hv3 | hv3
  · rw [s226w_cl1 (by linarith), s226w_clid hv2 hv3, Real.one_rpow]
    rcases eq_or_lt_of_le hv3 with h | h
    · rw [h, Real.one_rpow]; linarith
    · have := h2 v hv2 h; nlinarith
  · rw [s226w_cl1 (by linarith), s226w_cl1 hv3]; linarith

lemma s226w_Phi_mono {e b C r : ℝ} (he : 0 < e) (hr : 0 < r)
    (h1 : ∀ u, 0 < u → u ≤ 1 → b*u ≤ 2*e + C*u^r)
    (h2 : ∀ s, 0 ≤ s → s < 1 → b*(1-s) ≤ 2*e + C*(1 - s^r)) :
    Monotone (s226w_Phi e b C r) :=
  monotone_of_deriv_nonneg (fun v => (s226w_Phideriv e b C hr v).differentiableAt)
    (fun v => by rw [(s226w_Phideriv e b C hr v).deriv]; exact s226w_Phid_nonneg he hr h1 h2 v)

lemma s226w_flat0 {Φ : ℝ → ℝ} (hm : Monotone Φ) {a c w d : ℝ} (hac : Φ a = Φ c)
    (haw : a < w) (hwc : w < c) (hd : HasDerivAt Φ d w) : d = 0 := by
  have hconst : ∀ y ∈ Ioo a c, Φ y = Φ w := fun y hy => by
    have := hm hy.1.le; have := hm hy.2.le; have := hm haw.le; have := hm hwc.le; linarith
  have : HasDerivAt Φ 0 w := (hasDerivAt_const w (Φ w)).congr_of_eventuallyEq
    (Filter.eventually_of_mem (Ioo_mem_nhds haw hwc) hconst)
  exact hd.unique this

lemma s226w_noflat {e b C r u1 u3 : ℝ} (he : 0 < e) (hC : 0 ≤ C) (hr : 0 < r) (h1 : 0 < u1)
    (h13 : u1 < u3) (g1 : 2*e - b*u1 + C*u1^r = 0)
    (g2 : 2*e - b*((u1+u3)/2) + C*((u1+u3)/2)^r = 0) (g3 : 2*e - b*u3 + C*u3^r = 0) : False := by
  rcases eq_or_lt_of_le hC with hC0 | hCp
  · subst hC0
    have hb : 0 < b := by by_contra hb; push_neg at hb; nlinarith
    nlinarith [mul_pos hb (sub_pos.2 h13)]
  rcases lt_trichotomy r 1 with hr1 | hr1 | hr1
  · have := (Real.strictConcaveOn_rpow hr hr1).2 (mem_Ici.2 h1.le) (mem_Ici.2 (by linarith : (0:ℝ) ≤ u3))
      (ne_of_lt h13) (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2) (by norm_num)
    simp only [smul_eq_mul] at this
    have e2 : (1/2:ℝ)*u1 + (1/2)*u3 = (u1+u3)/2 := by ring
    rw [e2] at this
    nlinarith [mul_lt_mul_of_pos_left this hCp]
  · subst hr1
    simp only [Real.rpow_one] at g1 g2 g3
    have : (b - C)*(u3 - u1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · have : b = C := by linarith
      subst this; linarith
    · linarith
  · have := (strictConvexOn_rpow hr1).2 (mem_Ici.2 h1.le) (mem_Ici.2 (by linarith : (0:ℝ) ≤ u3))
      (ne_of_lt h13) (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2) (by norm_num)
    simp only [smul_eq_mul] at this
    have e2 : (1/2:ℝ)*u1 + (1/2)*u3 = (u1+u3)/2 := by ring
    rw [e2] at this
    nlinarith [mul_lt_mul_of_pos_left this hCp]

lemma s226w_Phi_neg {e b C r : ℝ} (he : 0 < e) (hC : 0 ≤ C) (hr : 0 < r)
    (h1 : ∀ u, 0 < u → u ≤ 1 → b*u ≤ 2*e + C*u^r)
    (h2 : ∀ s, 0 ≤ s → s < 1 → b*(1-s) ≤ 2*e + C*(1 - s^r)) {v : ℝ} (hv : v < 0) :
    s226w_Phi e b C r v < s226w_Phi e b C r 0 := by
  have hm := s226w_Phi_mono he hr h1 h2
  rcases lt_or_eq_of_le (hm hv.le) with h | h
  · exact h
  exfalso
  set lo := max v (-1/2) with hlodef
  have hlo : lo < 0 := max_lt hv (by norm_num)
  have hlo2 : -1/2 ≤ lo := le_max_right _ _
  have hvlo : v ≤ lo := le_max_left _ _
  have key : ∀ w, lo < w → w < 0 → 2*e - b*(w+1) + C*(w+1)^r = 0 := by
    intro w hw1 hw2
    have := s226w_flat0 hm h (by linarith : v < w) hw2 (s226w_Phideriv e b C hr w)
    unfold s226w_f at this
    rw [s226w_clid (by linarith) (by linarith), s226w_cl0 hw2.le, Real.zero_rpow hr.ne'] at this
    linarith
  have k1 := key (3*lo/4) (by linarith) (by linarith)
  have k2 := key (lo/2) (by linarith) (by linarith)
  have k3 := key (lo/4) (by linarith) (by linarith)
  have e2 : ((3*lo/4+1) + (lo/4+1))/2 = lo/2+1 := by ring
  exact s226w_noflat he hC hr (u1 := 3*lo/4+1) (u3 := lo/4+1) (by linarith) (by linarith) k1
    (by rw [e2]; exact k2) k3

lemma s226w_avg (p : Model) (hε : 0 < p.ε) (t K : ℝ) (f : ℝ → ℝ) (hf : Continuous f) (x : ℝ) :
    ∫ θ, (θ + K + f ((θ + p.ε - t)/(2*p.ε))) ∂posterior p x =
      x + K + (∫ w in (0:ℝ)..((x-t)/(2*p.ε)+1), f w) - ∫ w in (0:ℝ)..((x-t)/(2*p.ε)), f w := by
  rw [s226w_int p hε]
  have hc : (2*p.ε)⁻¹ ≠ 0 := inv_ne_zero (by linarith)
  have hsub : ∫ θ in (x-p.ε)..(x+p.ε), f ((θ + p.ε - t)/(2*p.ε)) =
      2*p.ε * ∫ w in ((x-t)/(2*p.ε))..((x-t)/(2*p.ε)+1), f w := by
    have e1 : ∀ θ, (θ + p.ε - t)/(2*p.ε) = (2*p.ε)⁻¹ * θ + (p.ε - t)/(2*p.ε) := fun θ => by
      field_simp; ring
    simp_rw [e1]
    rw [intervalIntegral.integral_comp_mul_add f hc, inv_inv, smul_eq_mul]
    have ha : (2*p.ε)⁻¹ * (x - p.ε) + (p.ε - t)/(2*p.ε) = (x-t)/(2*p.ε) := by field_simp; ring
    have hb : (2*p.ε)⁻¹ * (x + p.ε) + (p.ε - t)/(2*p.ε) = (x-t)/(2*p.ε) + 1 := by
      field_simp; ring
    rw [ha, hb]
  rw [intervalIntegral.integral_add (f := fun θ => θ + K) (g := fun θ => f ((θ + p.ε - t)/(2*p.ε)))
      ((by fun_prop : Continuous (fun θ:ℝ => θ + K)).intervalIntegrable _ _)
      ((hf.comp (by fun_prop : Continuous (fun θ:ℝ => (θ + p.ε - t)/(2*p.ε)))).intervalIntegrable _ _),
    hsub, intervalIntegral.integral_add (f := fun θ => θ) (g := fun _ => K)
      (continuous_id.intervalIntegrable _ _) (continuous_const.intervalIntegrable _ _),
    integral_id, intervalIntegral.integral_const, smul_eq_mul,
    ← intervalIntegral.integral_interval_sub_left (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]
  field_simp; ring

lemma s226w_mem1 {e C r t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    (2*e + C*t^r)/t ∈ thresholdRatios e C r := Or.inl ⟨t, ⟨ht0, ht1⟩, rfl⟩
lemma s226w_mem2 {e C r s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1) :
    (2*e + C*(1 - s^r))/(1-s) ∈ thresholdRatios e C r := Or.inr ⟨s, ⟨hs0, hs1⟩, rfl⟩
lemma s226w_bdd {e C r : ℝ} (he : 0 ≤ e) (hC : 0 ≤ C) (hr : 0 < r) :
    BddBelow (thresholdRatios e C r) := by
  refine ⟨0, ?_⟩
  rintro y (⟨t, ⟨h0, h1⟩, rfl⟩ | ⟨s, ⟨h0, h1⟩, rfl⟩)
  · exact div_nonneg (add_nonneg (by linarith) (mul_nonneg hC (Real.rpow_nonneg h0.le r))) h0.le
  · have : s^r ≤ 1 := Real.rpow_le_one h0 h1.le hr.le
    exact div_nonneg (by nlinarith) (by linarith)
lemma s226w_ne (e C r : ℝ) : (thresholdRatios e C r).Nonempty :=
  ⟨_, s226w_mem1 (e := e) (C := C) (r := r) one_pos le_rfl⟩
lemma s226w_le1 {e C r t : ℝ} (he : 0 ≤ e) (hC : 0 ≤ C) (hr : 0 < r) (ht0 : 0 < t) (ht1 : t ≤ 1) :
    competitionBound e C r ≤ (2*e + C*t^r)/t := csInf_le (s226w_bdd he hC hr) (s226w_mem1 ht0 ht1)
lemma s226w_le2 {e C r s : ℝ} (he : 0 ≤ e) (hC : 0 ≤ C) (hr : 0 < r) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    competitionBound e C r ≤ (2*e + C*(1 - s^r))/(1-s) :=
  csInf_le (s226w_bdd he hC hr) (s226w_mem2 hs0 hs1)

lemma s226w_ge2e {e C r : ℝ} (he : 0 < e) (hC : 0 ≤ C) (hr : 0 < r) :
    2*e ≤ competitionBound e C r := by
  apply le_csInf (s226w_ne e C r)
  rintro y (⟨t, ⟨h0, h1⟩, rfl⟩ | ⟨s, ⟨h0, h1⟩, rfl⟩)
  · rw [le_div_iff₀ h0]; nlinarith [mul_nonneg hC (Real.rpow_nonneg h0.le r)]
  · have : s^r ≤ 1 := Real.rpow_le_one h0 h1.le hr.le
    rw [le_div_iff₀ (by linarith)]; nlinarith

lemma s226w_strictE {e1 e2 C r : ℝ} (he1 : 0 < e1) (h12 : e1 < e2) (hC : 0 ≤ C) (hr : 0 < r) :
    competitionBound e1 C r < competitionBound e2 C r := by
  have : competitionBound e1 C r + 2*(e2-e1) ≤ competitionBound e2 C r := by
    apply le_csInf (s226w_ne e2 C r)
    rintro y (⟨t, ⟨h0, h1⟩, rfl⟩ | ⟨s, ⟨h0, h1⟩, rfl⟩)
    · have hy := s226w_le1 (e := e1) (C := C) he1.le hC hr h0 h1
      have : (2*e2 + C*t^r)/t = (2*e1 + C*t^r)/t + 2*(e2-e1)/t := by field_simp; ring
      have h3 : 2*(e2-e1) ≤ 2*(e2-e1)/t := by
        rw [le_div_iff₀ h0]; nlinarith
      linarith
    · have hy := s226w_le2 (e := e1) (C := C) he1.le hC hr h0 h1
      have hs : 0 < 1 - s := by linarith
      have : (2*e2 + C*(1-s^r))/(1-s) = (2*e1 + C*(1-s^r))/(1-s) + 2*(e2-e1)/(1-s) := by
        field_simp; ring
      have h3 : 2*(e2-e1) ≤ 2*(e2-e1)/(1-s) := by
        rw [le_div_iff₀ hs]; nlinarith
      linarith
  linarith

lemma s226w_strictC {e C1 C2 r : ℝ} (he : 0 < e) (hC1 : 0 ≤ C1) (h12 : C1 < C2) (hr : 0 < r) :
    competitionBound e C1 r < competitionBound e C2 r := by
  have hB1 : competitionBound e C1 r ≤ 2*e + C1 := by
    have := s226w_le1 (e := e) (C := C1) (r := r) he.le hC1 hr one_pos le_rfl
    simpa using this
  set B1 := competitionBound e C1 r
  set t0 := 2*e/(2*e + C1 + 1) with ht0def
  have ht0 : 0 < t0 := div_pos (by linarith) (by linarith)
  have ht01 : t0 < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hkey : 2*e/t0 = 2*e + C1 + 1 := by rw [ht0def]; field_simp
  have hpw : (1-t0)^r < 1 := Real.rpow_lt_one (by linarith) (by linarith) hr
  set δ := (C2 - C1) * min (t0^r) (1 - (1-t0)^r) with hδdef
  have hδ : 0 < δ := mul_pos (by linarith) (lt_min (Real.rpow_pos_of_pos ht0 r) (by linarith))
  have hC2 : 0 ≤ C2 := by linarith
  have : B1 + min 1 δ ≤ competitionBound e C2 r := by
    apply le_csInf (s226w_ne e C2 r)
    rintro y (⟨t, ⟨h0, h1⟩, rfl⟩ | ⟨s, ⟨h0, h1⟩, rfl⟩)
    · rcases le_total t t0 with htt | htt
      · have ha : 2*e/t0 ≤ 2*e/t := div_le_div_of_nonneg_left (by linarith) h0 htt
        have hb : 2*e/t ≤ (2*e + C2*t^r)/t :=
          div_le_div_of_nonneg_right (by nlinarith [mul_nonneg hC2 (Real.rpow_nonneg h0.le r)]) h0.le
        have := min_le_left 1 δ; linarith
      · have hy := s226w_le1 (e := e) (C := C1) he.le hC1 hr h0 h1
        have hsplit : (2*e + C2*t^r)/t = (2*e + C1*t^r)/t + (C2-C1)*t^r/t := by field_simp; ring
        have hpow : t0^r ≤ t^r := Real.rpow_le_rpow ht0.le htt hr.le
        have hX : 0 ≤ (C2-C1)*t^r := mul_nonneg (by linarith) (Real.rpow_nonneg h0.le r)
        have h3 : (C2-C1)*t^r ≤ (C2-C1)*t^r/t := by
          rw [le_div_iff₀ h0]; nlinarith [mul_le_mul_of_nonneg_left h1 hX]
        have h4 : δ ≤ (C2-C1)*t^r :=
          mul_le_mul_of_nonneg_left ((min_le_left _ _).trans hpow) (by linarith)
        have := min_le_right 1 δ; linarith
    · have hs : 0 < 1 - s := by linarith
      have hsr : s^r ≤ 1 := Real.rpow_le_one h0 h1.le hr.le
      rcases le_total (1-s) t0 with htt | htt
      · have ha : 2*e/t0 ≤ 2*e/(1-s) := div_le_div_of_nonneg_left (by linarith) hs htt
        have hb : 2*e/(1-s) ≤ (2*e + C2*(1-s^r))/(1-s) :=
          div_le_div_of_nonneg_right (by nlinarith) hs.le
        have := min_le_left 1 δ; linarith
      · have hy := s226w_le2 (e := e) (C := C1) he.le hC1 hr h0 h1
        have hsplit : (2*e + C2*(1-s^r))/(1-s) = (2*e + C1*(1-s^r))/(1-s) + (C2-C1)*(1-s^r)/(1-s) := by
          field_simp; ring
        have hpow : s^r ≤ (1-t0)^r := Real.rpow_le_rpow h0 (by linarith) hr.le
        have hX : 0 ≤ (C2-C1)*(1-s^r) := mul_nonneg (by linarith) (by linarith)
        have h3 : (C2-C1)*(1-s^r) ≤ (C2-C1)*(1-s^r)/(1-s) := by
          rw [le_div_iff₀ hs]; nlinarith [mul_le_mul_of_nonneg_left (by linarith : 1 - s ≤ 1) hX]
        have h4 : δ ≤ (C2-C1)*(1-s^r) :=
          mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (by linarith)) (by linarith)
        have := min_le_right 1 δ; linarith
  have := lt_min one_pos hδ; linarith

noncomputable def s226w_g (e b C r v : ℝ) : ℝ := 2*e + s226w_f b C r (v+1) - s226w_f b C r v

lemma s226w_gc (e b C : ℝ) {r : ℝ} (hr : 0 < r) : Continuous (s226w_g e b C r) := by
  unfold s226w_g
  have := s226w_fc b C hr
  exact (continuous_const.add (this.comp (continuous_id.add continuous_const))).sub this

lemma s226w_gout1 {e b C r v : ℝ} (hr : 0 < r) (hv : v ≤ -1) : s226w_g e b C r v = 2*e := by
  unfold s226w_g s226w_f
  rw [s226w_cl0 (by linarith : v+1 ≤ 0), s226w_cl0 (by linarith : v ≤ 0), Real.zero_rpow hr.ne']; ring
lemma s226w_gout2 {e b C r v : ℝ} (hv : 1 ≤ v) : s226w_g e b C r v = 2*e := by
  unfold s226w_g s226w_f
  rw [s226w_cl1 (by linarith : 1 ≤ v+1), s226w_cl1 hv]; ring
lemma s226w_gphi {e b C r v : ℝ} (hr : 0 < r) (h0 : -1 ≤ v) (h1 : v ≤ 0) :
    s226w_g e b C r v = 2*e - b*(v+1) + C*(v+1)^r := by
  unfold s226w_g s226w_f
  rw [s226w_clid (by linarith) (by linarith : v+1 ≤ 1), s226w_cl0 h1, Real.zero_rpow hr.ne']; ring
lemma s226w_gpsi {e b C r v : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ 1) :
    s226w_g e b C r v = 2*e - b*(1-v) + C*(1 - v^r) := by
  unfold s226w_g s226w_f
  rw [s226w_cl1 (by linarith : 1 ≤ v+1), s226w_clid h0 h1, Real.one_rpow]; ring

lemma s226w_cvx3 {r : ℝ} (hr : 1 ≤ r) {x y z : ℝ} (hx : 0 ≤ x) (hxy : x < y) (hyz : y < z) :
    (z-x)*y^r ≤ (z-y)*x^r + (y-x)*z^r := by
  have hzx : 0 < z - x := by linarith
  have hc := (convexOn_rpow hr).2 (mem_Ici.2 hx) (mem_Ici.2 (by linarith : (0:ℝ) ≤ z))
    (div_nonneg (by linarith : (0:ℝ) ≤ z - y) hzx.le) (div_nonneg (by linarith : (0:ℝ) ≤ y - x) hzx.le)
    (by rw [← add_div, div_eq_one_iff_eq hzx.ne']; ring)
  simp only [smul_eq_mul] at hc
  have hy : (z-y)/(z-x)*x + (y-x)/(z-x)*z = y := by field_simp; ring
  rw [hy] at hc
  calc (z-x)*y^r ≤ (z-x)*((z-y)/(z-x)*x^r + (y-x)/(z-x)*z^r) := mul_le_mul_of_nonneg_left hc hzx.le
    _ = _ := by first | (field_simp; ring) | field_simp

lemma s226w_ccv3 {r : ℝ} (hr0 : 0 < r) (hr : r ≤ 1) {x y z : ℝ} (hx : 0 ≤ x) (hxy : x < y) (hyz : y < z) :
    (z-y)*x^r + (y-x)*z^r ≤ (z-x)*y^r := by
  have hzx : 0 < z - x := by linarith
  have hc := (Real.concaveOn_rpow hr0.le hr).2 (mem_Ici.2 hx) (mem_Ici.2 (by linarith : (0:ℝ) ≤ z))
    (div_nonneg (by linarith : (0:ℝ) ≤ z - y) hzx.le) (div_nonneg (by linarith : (0:ℝ) ≤ y - x) hzx.le)
    (by rw [← add_div, div_eq_one_iff_eq hzx.ne']; ring)
  simp only [smul_eq_mul] at hc
  have hy : (z-y)/(z-x)*x + (y-x)/(z-x)*z = y := by field_simp; ring
  rw [hy] at hc
  calc (z-y)*x^r + (y-x)*z^r = (z-x)*((z-y)/(z-x)*x^r + (y-x)/(z-x)*z^r) := by
        first | (field_simp; ring) | field_simp
    _ ≤ (z-x)*y^r := mul_le_mul_of_nonneg_left hc hzx.le

lemma s226w_P1 {e b C r u1 u2 : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (hC : 0 ≤ C) (he : 0 < e)
    (hu1 : 0 < u1) (h12 : u1 < u2) (h : 2*e - b*u1 + C*u1^r < 0) : 2*e - b*u2 + C*u2^r < 0 := by
  have key := s226w_ccv3 hr0 hr1 le_rfl hu1 h12
  rw [Real.zero_rpow hr0.ne'] at key
  have h2 : u1 * (2*e - b*u2 + C*u2^r) < 0 := by
    nlinarith [mul_le_mul_of_nonneg_left key hC, mul_lt_mul_of_pos_left h (by linarith : 0 < u2)]
  by_contra hc; push_neg at hc; nlinarith [mul_nonneg hu1.le hc]

lemma s226w_P2 {e b C r s1 s2 s3 : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (hC : 0 ≤ C)
    (hs1 : 0 ≤ s1) (h12 : s1 < s2) (h23 : s2 < s3)
    (g1 : 2*e - b*(1-s1) + C*(1 - s1^r) < 0) (g3 : 2*e - b*(1-s3) + C*(1 - s3^r) < 0) :
    2*e - b*(1-s2) + C*(1 - s2^r) < 0 := by
  have key := s226w_ccv3 hr0 hr1 hs1 h12 h23
  have h2 : (s3 - s1) * (2*e - b*(1-s2) + C*(1 - s2^r)) < 0 := by
    nlinarith [mul_le_mul_of_nonneg_left key hC, mul_lt_mul_of_pos_left g1 (by linarith : 0 < s3 - s2),
      mul_lt_mul_of_pos_left g3 (by linarith : 0 < s2 - s1)]
  by_contra hc; push_neg at hc; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ s3 - s1) hc]

lemma s226w_P3 {e b C r u1 u2 u3 : ℝ} (hr1 : 1 ≤ r) (hC : 0 ≤ C)
    (hu1 : 0 ≤ u1) (h12 : u1 < u2) (h23 : u2 < u3)
    (g1 : 2*e - b*u1 + C*u1^r < 0) (g3 : 2*e - b*u3 + C*u3^r < 0) : 2*e - b*u2 + C*u2^r < 0 := by
  have key := s226w_cvx3 hr1 hu1 h12 h23
  have h2 : (u3 - u1) * (2*e - b*u2 + C*u2^r) < 0 := by
    nlinarith [mul_le_mul_of_nonneg_left key hC, mul_lt_mul_of_pos_left g1 (by linarith : 0 < u3 - u2),
      mul_lt_mul_of_pos_left g3 (by linarith : 0 < u2 - u1)]
  by_contra hc; push_neg at hc; nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ u3 - u1) hc]

lemma s226w_P4 {e b C r s2 s3 : ℝ} (hr1 : 1 ≤ r) (hC : 0 ≤ C) (he : 0 < e)
    (hs2 : 0 ≤ s2) (h23 : s2 < s3) (hs3 : s3 < 1)
    (g3 : 2*e - b*(1-s3) + C*(1 - s3^r) < 0) : 2*e - b*(1-s2) + C*(1 - s2^r) < 0 := by
  have key := s226w_cvx3 hr1 hs2 h23 hs3
  rw [Real.one_rpow] at key
  by_contra hc; push_neg at hc
  nlinarith [mul_le_mul_of_nonneg_left key hC, mul_nonneg (by linarith : (0:ℝ) ≤ 1 - s3) hc,
    mul_lt_mul_of_pos_left g3 (by linarith : 0 < 1 - s2), mul_pos he (by linarith : (0:ℝ) < s3 - s2)]

lemma s226w_oc {e b C r v1 v2 v3 : ℝ} (he : 0 < e) (hC : 0 ≤ C) (hr : 0 < r)
    (h12 : v1 < v2) (h23 : v2 < v3) (g1 : s226w_g e b C r v1 < 0) (g3 : s226w_g e b C r v3 < 0) :
    s226w_g e b C r v2 < 0 := by
  have hv1 : -1 < v1 := by
    by_contra h; push_neg at h; rw [s226w_gout1 hr h] at g1; linarith
  have hv3 : v3 < 1 := by
    by_contra h; push_neg at h; rw [s226w_gout2 h] at g3; linarith
  rcases le_total r 1 with hr1 | hr1
  · -- φ: negatives propagate right; ψ convex
    have prop : ∀ w, v1 < w → w ≤ 0 → s226w_g e b C r w < 0 := by
      intro w hw1 hw2
      have g1' := g1
      rw [s226w_gphi hr hv1.le (by linarith)] at g1'
      rw [s226w_gphi hr (by linarith) hw2]
      by_cases hpos : 0 < v1 + 1
      · exact s226w_P1 hr hr1 hC he hpos (by linarith) g1'
      · linarith
    rcases le_total v2 0 with h2 | h2
    · exact prop v2 h12 h2
    rcases le_total 0 v1 with h1 | h1
    · rw [s226w_gpsi h1 (by linarith)] at g1
      rw [s226w_gpsi (by linarith) hv3.le] at g3
      rw [s226w_gpsi h2 (by linarith)]
      exact s226w_P2 hr hr1 hC h1 h12 h23 g1 g3
    · have g0 : s226w_g e b C r 0 < 0 := by
        rcases eq_or_lt_of_le h1 with h | h
        · have e0 : s226w_g e b C r 0 = s226w_g e b C r v1 := by rw [h]
          rw [e0]; exact g1
        · exact prop 0 h le_rfl
      rcases eq_or_lt_of_le h2 with h | h
      · rw [← h]; exact g0
      rw [s226w_gpsi le_rfl zero_le_one] at g0
      rw [s226w_gpsi (by linarith) hv3.le] at g3
      rw [s226w_gpsi h2 (by linarith)]
      exact s226w_P2 hr hr1 hC le_rfl h h23 g0 g3
  · -- φ convex; ψ negatives propagate left
    have prop : ∀ w, 0 ≤ w → w < v3 → s226w_g e b C r w < 0 := by
      intro w hw1 hw2
      have g3' := g3
      rw [s226w_gpsi (by linarith) hv3.le] at g3'
      rw [s226w_gpsi hw1 (by linarith)]
      exact s226w_P4 hr1 hC he hw1 hw2 hv3 g3'
    rcases le_total 0 v2 with h2 | h2
    · exact prop v2 h2 h23
    rcases le_total v3 0 with h3 | h3
    · rw [s226w_gphi hr hv1.le (by linarith)] at g1
      rw [s226w_gphi hr (by linarith) h3] at g3
      rw [s226w_gphi hr (by linarith) h2]
      exact s226w_P3 hr1 hC (by linarith) (by linarith) (by linarith) g1 g3
    · have g0 : s226w_g e b C r 0 < 0 := by
        rcases eq_or_lt_of_le h3 with h | h
        · have e0 : s226w_g e b C r 0 = s226w_g e b C r v3 := by rw [h]
          rw [e0]; exact g3
        · exact prop 0 le_rfl h
      rcases eq_or_lt_of_le h2 with h | h
      · rw [h]; exact g0
      rw [s226w_gphi hr (by norm_num) le_rfl] at g0
      rw [s226w_gphi hr hv1.le (by linarith)] at g1
      rw [s226w_gphi hr (by linarith) h2]
      exact s226w_P3 hr1 hC (by linarith) (by linarith) (by linarith) g1 g0

lemma s226w_noflatpsi {e b C r s1 s3 : ℝ} (he : 0 < e) (hC : 0 ≤ C) (hr : 0 < r) (h1 : 0 ≤ s1)
    (h13 : s1 < s3) (g1 : 2*e - b*(1-s1) + C*(1 - s1^r) = 0)
    (g2 : 2*e - b*(1-(s1+s3)/2) + C*(1 - ((s1+s3)/2)^r) = 0)
    (g3 : 2*e - b*(1-s3) + C*(1 - s3^r) = 0) : False := by
  rcases eq_or_lt_of_le hC with hC0 | hCp
  · subst hC0
    have : b*(s3 - s1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · subst h; linarith
    · linarith
  rcases lt_trichotomy r 1 with hr1 | hr1 | hr1
  · have := (Real.strictConcaveOn_rpow hr hr1).2 (mem_Ici.2 h1) (mem_Ici.2 (by linarith : (0:ℝ) ≤ s3))
      (ne_of_lt h13) (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2) (by norm_num)
    simp only [smul_eq_mul] at this
    have e2 : (1/2:ℝ)*s1 + (1/2)*s3 = (s1+s3)/2 := by ring
    rw [e2] at this
    nlinarith [mul_lt_mul_of_pos_left this hCp]
  · subst hr1
    simp only [Real.rpow_one] at g1 g2 g3
    have : (b - C)*(s3 - s1) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · have : b = C := by linarith
      subst this; linarith
    · linarith
  · have := (strictConvexOn_rpow hr1).2 (mem_Ici.2 h1) (mem_Ici.2 (by linarith : (0:ℝ) ≤ s3))
      (ne_of_lt h13) (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2) (by norm_num)
    simp only [smul_eq_mul] at this
    have e2 : (1/2:ℝ)*s1 + (1/2)*s3 = (s1+s3)/2 := by ring
    rw [e2] at this
    nlinarith [mul_lt_mul_of_pos_left this hCp]

lemma s226w_gnz {e b C r : ℝ} (he : 0 < e) (hC : 0 ≤ C) (hr : 0 < r) {x y : ℝ} (hxy : x < y) :
    ∃ w ∈ Ioo x y, s226w_g e b C r w ≠ 0 := by
  by_contra hcon; push_neg at hcon
  rcases lt_or_ge x (-1) with hx | hx
  · have hm : x < min y (-1) := lt_min hxy hx
    have hw := hcon ((x + min y (-1))/2) ⟨by linarith, by linarith [min_le_left y (-1)]⟩
    rw [s226w_gout1 hr (by linarith [min_le_right y (-1)])] at hw; linarith
  rcases lt_or_ge x 0 with hx0 | hx0
  · set m := min y 0 with hmdef
    have hm : x < m := lt_min hxy hx0
    have hmy : m ≤ y := min_le_left _ _
    have hm0 : m ≤ 0 := min_le_right _ _
    have z : ∀ k : ℝ, 0 < k → k < 1 →
        2*e - b*((x + k*(m-x))+1) + C*((x + k*(m-x))+1)^r = 0 := by
      intro k hk0 hk1
      have hkm : 0 < k*(m-x) := mul_pos hk0 (by linarith)
      have hkm2 : k*(m-x) < m - x := by nlinarith
      have := hcon (x + k*(m-x)) ⟨by linarith, by linarith⟩
      rwa [s226w_gphi hr (by linarith) (by linarith)] at this
    have z1 := z (1/4) (by norm_num) (by norm_num)
    have z2 := z (1/2) (by norm_num) (by norm_num)
    have z3 := z (3/4) (by norm_num) (by norm_num)
    have e2 : ((x + 1/4*(m-x) + 1) + (x + 3/4*(m-x) + 1))/2 = x + 1/2*(m-x) + 1 := by ring
    exact s226w_noflat he hC hr (u1 := x + 1/4*(m-x) + 1) (u3 := x + 3/4*(m-x) + 1)
      (by linarith) (by linarith) z1 (by rw [e2]; exact z2) z3
  rcases lt_or_ge x 1 with hx1 | hx1
  · set m := min y 1 with hmdef
    have hm : x < m := lt_min hxy hx1
    have hmy : m ≤ y := min_le_left _ _
    have hm1 : m ≤ 1 := min_le_right _ _
    have z : ∀ k : ℝ, 0 < k → k < 1 →
        2*e - b*(1-(x + k*(m-x))) + C*(1 - (x + k*(m-x))^r) = 0 := by
      intro k hk0 hk1
      have hkm : 0 < k*(m-x) := mul_pos hk0 (by linarith)
      have hkm2 : k*(m-x) < m - x := by nlinarith
      have := hcon (x + k*(m-x)) ⟨by linarith, by linarith⟩
      rwa [s226w_gpsi (by linarith) (by linarith)] at this
    have z1 := z (1/4) (by norm_num) (by norm_num)
    have z2 := z (1/2) (by norm_num) (by norm_num)
    have z3 := z (3/4) (by norm_num) (by norm_num)
    have e2 : ((x + 1/4*(m-x)) + (x + 3/4*(m-x)))/2 = x + 1/2*(m-x) := by ring
    exact s226w_noflatpsi he hC hr (s1 := x + 1/4*(m-x)) (s3 := x + 3/4*(m-x))
      (by nlinarith) (by linarith) z1 (by rw [e2]; exact z2) z3
  · have hw := hcon ((x + y)/2) ⟨by linarith, by linarith⟩
    rw [s226w_gout2 (by linarith)] at hw; linarith

lemma s226w_smono {Φ g : ℝ → ℝ} (hd : ∀ v, HasDerivAt Φ (g v) v) {x y : ℝ} (hxy : x < y)
    (hg : ∀ w ∈ Ioo x y, 0 ≤ g w) (hw : ∃ w ∈ Ioo x y, g w ≠ 0) : Φ x < Φ y := by
  have hmono : MonotoneOn Φ (Icc x y) := monotoneOn_of_deriv_nonneg (convex_Icc x y)
    (fun v _ => (hd v).continuousAt.continuousWithinAt)
    (fun v _ => (hd v).differentiableAt.differentiableWithinAt)
    (fun v hv => by rw [interior_Icc] at hv; rw [(hd v).deriv]; exact hg v hv)
  rcases lt_or_eq_of_le (hmono (left_mem_Icc.2 hxy.le) (right_mem_Icc.2 hxy.le) hxy.le) with h | h
  · exact h
  obtain ⟨w, hw, hgw⟩ := hw
  exfalso; apply hgw
  have hconst : ∀ z ∈ Ioo x y, Φ z = Φ w := fun z hz => by
    have a1 := hmono (left_mem_Icc.2 hxy.le) (Ioo_subset_Icc_self hz) hz.1.le
    have a2 := hmono (Ioo_subset_Icc_self hz) (right_mem_Icc.2 hxy.le) hz.2.le
    have a3 := hmono (left_mem_Icc.2 hxy.le) (Ioo_subset_Icc_self hw) hw.1.le
    have a4 := hmono (Ioo_subset_Icc_self hw) (right_mem_Icc.2 hxy.le) hw.2.le
    linarith
  have : HasDerivAt Φ 0 w := (hasDerivAt_const w (Φ w)).congr_of_eventuallyEq
    (Filter.eventually_of_mem (Ioo_mem_nhds hw.1 hw.2) hconst)
  exact (hd w).unique this

lemma s226w_santi {Φ g : ℝ → ℝ} (hd : ∀ v, HasDerivAt Φ (g v) v) {x y : ℝ} (hxy : x < y)
    (hg : ∀ w ∈ Ioo x y, g w < 0) : Φ y < Φ x := by
  have := s226w_smono (Φ := fun v => -Φ v) (g := fun v => -g v) (fun v => (hd v).neg) hxy
    (fun w hw => by show 0 ≤ -g w; linarith [hg w hw])
    ⟨(x+y)/2, ⟨by linarith, by linarith⟩, by
      show -g ((x+y)/2) ≠ 0; linarith [hg ((x+y)/2) ⟨by linarith, by linarith⟩]⟩
  exact neg_lt_neg_iff.1 this

/-- Shape of Φ when the bound fails. -/
lemma s226w_shape {e b C r : ℝ} (he : 0 < e) (hC : 0 ≤ C) (hr : 0 < r)
    (hbl : competitionBound e C r < b) :
    ∃ a c : ℝ, a < c ∧ StrictMonoOn (s226w_Phi e b C r) (Iic a) ∧
      StrictAntiOn (s226w_Phi e b C r) (Icc a c) ∧ StrictMonoOn (s226w_Phi e b C r) (Ici c) := by
  have hd : ∀ v, HasDerivAt (s226w_Phi e b C r) (s226w_g e b C r v) v :=
    fun v => s226w_Phideriv e b C hr v
  obtain ⟨y0, hy0, hlt⟩ := exists_lt_of_csInf_lt (s226w_ne e C r) hbl
  have hN : ∃ v0, s226w_g e b C r v0 < 0 := by
    rcases hy0 with ⟨u, ⟨h0, h1⟩, rfl⟩ | ⟨s, ⟨h0, h1⟩, rfl⟩
    · refine ⟨u - 1, ?_⟩
      rw [s226w_gphi hr (by linarith) (by linarith), sub_add_cancel]
      rw [div_lt_iff₀ h0] at hlt; linarith
    · refine ⟨s, ?_⟩
      rw [s226w_gpsi h0 h1.le]
      rw [div_lt_iff₀ (by linarith)] at hlt; linarith
  obtain ⟨v0, hv0⟩ := hN
  set N := {v | s226w_g e b C r v < 0} with hNdef
  have hv0N : v0 ∈ N := hv0
  have hbb : BddBelow N := ⟨-1, fun v hv => by
    by_contra h; push_neg at h
    have hv' : s226w_g e b C r v < 0 := hv
    rw [s226w_gout1 hr h.le] at hv'; linarith⟩
  have hba : BddAbove N := ⟨1, fun v hv => by
    by_contra h; push_neg at h
    have hv' : s226w_g e b C r v < 0 := hv
    rw [s226w_gout2 h.le] at hv'; linarith⟩
  have hopen : IsOpen N := isOpen_lt (s226w_gc e b C hr) continuous_const
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hopen v0 hv0N
  have hv0' : v0 + δ/2 ∈ N := hball (by
    rw [Metric.mem_ball, Real.dist_eq, abs_of_pos (by linarith)]; linarith)
  have ha : sInf N ≤ v0 := csInf_le hbb hv0N
  have hc : v0 + δ/2 ≤ sSup N := le_csSup hba hv0'
  have hin : ∀ w ∈ Ioo (sInf N) (sSup N), s226w_g e b C r w < 0 := by
    intro w hw
    obtain ⟨v1, hv1N, hv1⟩ := exists_lt_of_csInf_lt ⟨v0, hv0N⟩ hw.1
    obtain ⟨v3, hv3N, hv3⟩ := exists_lt_of_lt_csSup ⟨v0, hv0N⟩ hw.2
    exact s226w_oc he hC hr hv1 hv3 hv1N hv3N
  have hleft : ∀ w, w < sInf N → 0 ≤ s226w_g e b C r w := by
    intro w hw; by_contra h; push_neg at h
    have := csInf_le hbb (show w ∈ N from h); linarith
  have hright : ∀ w, sSup N < w → 0 ≤ s226w_g e b C r w := by
    intro w hw; by_contra h; push_neg at h
    have := le_csSup hba (show w ∈ N from h); linarith
  refine ⟨sInf N, sSup N, by linarith, ?_, ?_, ?_⟩
  · intro x hx y hy hxy
    exact s226w_smono hd hxy (fun w hw => hleft w (by linarith [hw.2, show y ≤ sInf N from hy]))
      (s226w_gnz he hC hr hxy)
  · intro x hx y hy hxy
    exact s226w_santi hd hxy (fun w hw => hin w ⟨by linarith [hw.1, hx.1], by linarith [hw.2, hy.2]⟩)
  · intro x hx y hy hxy
    exact s226w_smono hd hxy (fun w hw => hright w (by linarith [hw.1, show sSup N ≤ x from hx]))
      (s226w_gnz he hC hr hxy)

theorem s226w_l1 (p : Model) (hp : p.Valid) :
    2 * p.ε < followerBound p ∧
    StrictMonoOn (fun ε => competitionBound ε ((1 - p.q) * (p.fH - p.mL)) p.r) (Ioi 0) ∧
    StrictMonoOn (fun d => competitionBound p.ε ((1 - p.q) * d) p.r) (Ioi 0) ∧
    (p.b ≤ followerBound p →
      AdoptionEquilibrium p (regulation p) (thresholdProfile (adoptionCutoff p)) ∧
      (∀ θ, adoptionMass p (thresholdProfile (adoptionCutoff p)) θ =
        thresholdMass p (adoptionCutoff p) θ) ∧
      (∀ i ∈ Ico (0 : ℝ) 1, ∀ x,
        thresholdProfile (adoptionCutoff p) i x = true ↔ adoptionCutoff p ≤ x)) := by
  obtain ⟨hε, hb0, hq0, hq1, hr, -, hfL, hfLH, hmLH, hmH⟩ := hp
  have hq : 0 < 1 - p.q := by linarith
  have hC : 0 < (1 - p.q) * (p.fH - p.mL) := mul_pos hq (by linarith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc 2*p.ε ≤ competitionBound p.ε 0 p.r := s226w_ge2e hε le_rfl hr
      _ < _ := s226w_strictC hε le_rfl hC hr
  · intro e1 he1 e2 _ h12; exact s226w_strictE he1 h12 hC.le hr
  · intro d1 hd1 d2 _ h12
    exact s226w_strictC hε (mul_pos hq hd1).le (mul_lt_mul_of_pos_left h12 hq) hr
  intro hb
  set C := (1 - p.q) * (p.fH - p.mL) with hCdef
  set t := adoptionCutoff p with ht
  have h1 : ∀ u, 0 < u → u ≤ 1 → p.b*u ≤ 2*p.ε + C*u^p.r := fun u h0 h1 => by
    have := le_trans hb (s226w_le1 hε.le hC.le hr h0 h1); rwa [le_div_iff₀ h0] at this
  have h2 : ∀ s, 0 ≤ s → s < 1 → p.b*(1-s) ≤ 2*p.ε + C*(1 - s^p.r) := fun s h0 h1 => by
    have := le_trans hb (s226w_le2 hε.le hC.le hr h0 h1)
    rwa [le_div_iff₀ (by linarith)] at this
  have hmass : ∀ θ, adoptionMass p (thresholdProfile t) θ = thresholdMass p t θ :=
    s226w_mass p hε t
  have htc := s226w_tmc p t
  have hcont : ∀ a, Continuous (fun θ => followerPayoff p (regulation p) a θ (thresholdMass p t θ)) := by
    intro a
    have hα : Continuous (fun θ => thresholdMass p t θ ^ p.r) := htc.rpow_const (fun _ => Or.inr hr.le)
    cases a
    · simp only [followerPayoff, regulation, Bool.false_eq_true, if_false]
      exact (continuous_const.add (continuous_const.mul hα)).mul continuous_const
    · simp only [followerPayoff, regulation, if_true]
      exact ((((continuous_const.add continuous_id).sub (continuous_const.mul htc)).add
        ((continuous_const.add (continuous_const.mul hα)).mul continuous_const)).add
        ((continuous_const.sub (continuous_const.add (continuous_const.mul hα))).mul continuous_const))
  set K0 := -p.fL + p.mL + p.q*(p.fH - p.mL) with hK0
  have hD : ∀ x, followerInterim p (regulation p) (thresholdProfile t) x true -
      followerInterim p (regulation p) (thresholdProfile t) x false =
      s226w_Phi p.ε p.b C p.r ((x-t)/(2*p.ε)) - s226w_Phi p.ε p.b C p.r 0 := by
    intro x
    unfold followerInterim expectation
    simp only [hmass]
    rw [← integral_sub (s226w_intg p hε (hcont true) x) (s226w_intg p hε (hcont false) x)]
    have hfun : (fun θ => followerPayoff p (regulation p) true θ (thresholdMass p t θ) -
        followerPayoff p (regulation p) false θ (thresholdMass p t θ)) =
        fun θ => θ + K0 + s226w_f p.b C p.r ((θ + p.ε - t)/(2*p.ε)) := by
      ext θ
      rw [show thresholdMass p t θ = s226w_cl ((θ + p.ε - t)/(2*p.ε)) from rfl]
      simp only [followerPayoff, regulation, if_true, Bool.false_eq_true, if_false, s226w_f]
      rw [hK0, hCdef]; ring
    rw [hfun, s226w_avg p hε t K0 _ (s226w_fc p.b C hr)]
    have hF := s226w_F01 p.b C hr
    have hv : 2*p.ε*((x-t)/(2*p.ε)) = x - t := by field_simp
    have htK : t + K0 = p.b/2 - C/(p.r+1) := by
      rw [ht, hK0, hCdef]; unfold adoptionCutoff; field_simp; ring
    unfold s226w_Phi
    rw [zero_add]
    change x + K0 + s226w_F p.b C p.r ((x - t) / (2 * p.ε) + 1) - s226w_F p.b C p.r ((x - t) / (2 * p.ε)) = _
    linarith
  have hpos : ∀ x, t ≤ x → 0 ≤ s226w_Phi p.ε p.b C p.r ((x-t)/(2*p.ε)) - s226w_Phi p.ε p.b C p.r 0 :=
    fun x hx => sub_nonneg.2 (s226w_Phi_mono hε hr h1 h2 (div_nonneg (by linarith) (by linarith)))
  have hneg : ∀ x, x < t → s226w_Phi p.ε p.b C p.r ((x-t)/(2*p.ε)) - s226w_Phi p.ε p.b C p.r 0 < 0 :=
    fun x hx => sub_neg.2 (s226w_Phi_neg hε hC.le hr h1 h2 (div_neg_of_neg_of_pos (by linarith) (by linarith)))
  have hAE : AdoptionEquilibrium p (regulation p) (thresholdProfile t) := by
    refine ⟨?_, ?_, ?_⟩
    · unfold Profile.Measurable thresholdProfile
      apply measurable_to_bool
      have : ((fun z : ℝ × ℝ => decide (t ≤ z.2)) ⁻¹' {true}) = {z | t ≤ z.2} := by
        ext z; simp
      rw [this]; exact measurableSet_le measurable_const measurable_snd
    · intro x a; simp only [hmass]; exact s226w_intg p hε (hcont a) x
    · intro i _ x
      have hσ : thresholdProfile t i x = decide (t ≤ x) := rfl
      rw [hσ]
      by_cases hx : t ≤ x
      · simp only [hx, decide_true]
        refine ⟨fun a => ?_, ?_⟩
        · cases a
          · linarith [hD x, hpos x hx]
          · exact le_rfl
        · simp
      · simp only [hx, decide_false]
        push_neg at hx
        refine ⟨fun a => ?_, fun h => ?_⟩
        · cases a
          · exact le_rfl
          · linarith [hD x, hneg x hx]
        · exfalso; linarith [hD x, hneg x hx]
  exact ⟨hAE, hmass, fun i _ x => by simp [thresholdProfile]⟩

lemma s226w_Fdiff {b C r : ℝ} (hb0 : 0 ≤ b) (hC : 0 ≤ C) (hr : 0 < r) (v : ℝ) :
    |s226w_F b C r (v+1) - s226w_F b C r v| ≤ b + C := by
  have hfc := s226w_fc b C hr
  unfold s226w_F
  rw [intervalIntegral.integral_interval_sub_left (hfc.intervalIntegrable _ _) (hfc.intervalIntegrable _ _)]
  have hfb : ∀ w, ‖s226w_f b C r w‖ ≤ b + C := by
    intro w
    have h0 : 0 ≤ s226w_cl w := le_min zero_le_one (le_max_left _ _)
    have h1 : s226w_cl w ≤ 1 := min_le_left _ _
    have hp0 : 0 ≤ s226w_cl w ^ r := Real.rpow_nonneg h0 r
    have hp1 : s226w_cl w ^ r ≤ 1 := Real.rpow_le_one h0 h1 hr.le
    rw [Real.norm_eq_abs, abs_le]; unfold s226w_f
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left h1 hb0, mul_le_mul_of_nonneg_left hp1 hC,
      mul_nonneg hb0 h0, mul_nonneg hC hp0]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := v) (b := v+1)
    (fun w _ => hfb w)
  simpa [Real.norm_eq_abs] using this

theorem solution (p : Model) (hp : p.Valid) (hb : p.b ≤ followerBound p) :
    2 * p.ε ≤ leaderBound p ∧ leaderBound p < followerBound p ∧
    StrictMonoOn (fun ε => competitionBound ε ((1 - p.q) * (p.mH - p.mL)) p.r) (Ioi 0) ∧
    StrictMonoOn (fun d => competitionBound p.ε ((1 - p.q) * d) p.r) (Ici 0) ∧
    (∀ lam : ℝ, 0 ≤ lam →
      (developmentSet p lam).Nonempty ∧ BddBelow (developmentSet p lam) ∧
      SpecifiedBeliefEquilibrium p (regulation p) lam (thresholdProfile (adoptionCutoff p))
        (endogenousDecision p lam)) ∧
    (p.b ≤ leaderBound p → ∀ lam : ℝ, 0 ≤ lam →
      developmentSet p lam = Ici (developmentCutoff p lam)) ∧
    (leaderBound p < p.b → ∃ lamlo lamhi : ℝ, lamlo ≤ lamhi ∧
      ∀ lam : ℝ, 0 ≤ lam → ∃ x y z : ℝ, x = developmentCutoff p lam ∧ x ≤ y ∧ y ≤ z ∧
        ((lam < lamlo ∨ lamhi < lam) → developmentSet p lam = Ici x) ∧
        (lamlo ≤ lam ∧ lam ≤ lamhi → developmentSet p lam = Icc x y ∪ Ici z)) := by
  have hAE := ((s226w_l1 p hp).2.2.2 hb).1
  obtain ⟨hε, hb0, hq0, hq1, hr, -, hfL, hfLH, hmLH, hmH⟩ := hp
  have hq : 0 < 1 - p.q := by linarith
  have hD0 : 0 ≤ (1 - p.q) * (p.mH - p.mL) := mul_nonneg hq.le (by linarith)
  have hDC : (1 - p.q) * (p.mH - p.mL) < (1 - p.q) * (p.fH - p.mL) :=
    mul_lt_mul_of_pos_left (by linarith) hq
  refine ⟨s226w_ge2e hε hD0 hr, s226w_strictC hε hD0 hDC hr,
    fun e1 he1 e2 _ h12 => s226w_strictE he1 h12 hD0 hr,
    fun d1 hd1 d2 _ h12 => s226w_strictC hε (mul_nonneg hq.le hd1) (mul_lt_mul_of_pos_left h12 hq) hr,
    ?_⟩
  set D := (1 - p.q) * (p.mH - p.mL) with hDdef
  set t := adoptionCutoff p with ht
  set K0 := -p.f₁ + p.mL + p.q*(p.mH - p.mL) with hK0
  set W : ℝ → ℝ := fun x => s226w_Phi p.ε p.b D p.r ((x-t)/(2*p.ε)) + (t + K0) with hWdef
  have hU : ∀ lam x, endogenousUtility p lam x = lam + W x := by
    intro lam x
    unfold endogenousUtility expectation
    have hfun : (fun θ => leaderGain p lam θ (thresholdMass p t θ)) =
        fun θ => θ + (lam + K0) + s226w_f p.b D p.r ((θ + p.ε - t)/(2*p.ε)) := by
      ext θ
      rw [show thresholdMass p t θ = s226w_cl ((θ + p.ε - t)/(2*p.ε)) from rfl]
      simp only [leaderGain, regulation, s226w_f]
      rw [hK0, hDdef]; ring
    rw [hfun, s226w_avg p hε t (lam + K0) _ (s226w_fc p.b D hr)]
    have hv : 2*p.ε*((x-t)/(2*p.ε)) = x - t := by field_simp
    simp only [hWdef]
    unfold s226w_Phi s226w_F
    linarith
  have hΦd : Differentiable ℝ (s226w_Phi p.ε p.b D p.r) :=
    fun v => (s226w_Phideriv p.ε p.b D hr v).differentiableAt
  have hΦc : Continuous (s226w_Phi p.ε p.b D p.r) := hΦd.continuous
  have hWc : Continuous W :=
    (hΦc.comp ((continuous_id.sub continuous_const).div_const _)).add continuous_const
  have hWlo : ∀ x, x + K0 - (p.b + D) ≤ W x := by
    intro x
    have := (abs_le.1 (s226w_Fdiff hb0 hD0 hr ((x-t)/(2*p.ε)))).1
    have hv : 2*p.ε*((x-t)/(2*p.ε)) = x - t := by field_simp
    simp only [hWdef]; unfold s226w_Phi; linarith
  have hWhi : ∀ x, W x ≤ x + K0 + (p.b + D) := by
    intro x
    have := (abs_le.1 (s226w_Fdiff hb0 hD0 hr ((x-t)/(2*p.ε)))).2
    have hv : 2*p.ε*((x-t)/(2*p.ε)) = x - t := by field_simp
    simp only [hWdef]; unfold s226w_Phi; linarith
  have hset : ∀ lam, developmentSet p lam = {x | -lam ≤ W x} := by
    intro lam; ext x; simp only [developmentSet, mem_setOf_eq, hU]; constructor <;> intro h <;> linarith
  have hne : ∀ lam, (developmentSet p lam).Nonempty := fun lam =>
    ⟨p.b + D - K0 - lam, by rw [hset]; show -lam ≤ W _; linarith [hWlo (p.b + D - K0 - lam)]⟩
  have hbdd : ∀ lam, BddBelow (developmentSet p lam) := fun lam =>
    ⟨-lam - K0 - (p.b + D), fun x hx => by
      rw [hset] at hx; have : -lam ≤ W x := hx; linarith [hWhi x]⟩
  have hvle : ∀ x y, x ≤ y → (x-t)/(2*p.ε) ≤ (y-t)/(2*p.ε) :=
    fun x y h => div_le_div_of_nonneg_right (by linarith) (by linarith)
  have hvlt : ∀ x y, x < y → (x-t)/(2*p.ε) < (y-t)/(2*p.ε) :=
    fun x y h => div_lt_div_of_pos_right (by linarith) (by linarith)
  have hRc : Continuous (fun θ => thresholdMass p t θ ^ p.r) :=
    (s226w_tmc p t).rpow_const (fun _ => Or.inr hr.le)
  have hmass : ∀ θ, adoptionMass p (thresholdProfile t) θ = thresholdMass p t θ :=
    s226w_mass p hε t
  refine ⟨fun lam hlam => ⟨hne lam, hbdd lam, hAE, ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- measurability of the decision
    unfold endogenousDecision
    apply measurable_to_bool
    have : ((fun x => decide (0 ≤ endogenousUtility p lam x)) ⁻¹' {true}) =
        {x | 0 ≤ lam + W x} := by ext z; simp [hU]
    rw [this]; exact measurableSet_le measurable_const (continuous_const.add hWc).measurable
  · intro x a; simp only [hmass]; apply s226w_intg p hε
    have htc := s226w_tmc p t
    have hα := hRc
    cases a
    · simp only [leaderPayoff, Bool.false_eq_true, if_false]; exact continuous_const
    · simp only [leaderPayoff, regulation, if_true]
      exact ((((continuous_const.add continuous_id).sub (continuous_const.mul htc)).add
        ((continuous_const.add (continuous_const.mul hα)).mul continuous_const)).add
        ((continuous_const.sub (continuous_const.add (continuous_const.mul hα))).mul continuous_const))
  · intro x
    have hT : expectation p x (fun θ => leaderPayoff p (regulation p) lam true θ
        (adoptionMass p (thresholdProfile t) θ)) = endogenousUtility p lam x := by
      simp only [hmass]; unfold endogenousUtility; congr 1; ext θ
      simp only [leaderPayoff, leaderGain, if_true]; ring
    have hF : expectation p x (fun θ => leaderPayoff p (regulation p) lam false θ
        (adoptionMass p (thresholdProfile t) θ)) = 0 := by
      simp [expectation, leaderPayoff]
    refine ⟨fun a => ?_, fun h0 => ?_⟩
    · by_cases hx : 0 ≤ endogenousUtility p lam x
      · have hd : endogenousDecision p lam x = true := by simp [endogenousDecision, hx]
        rw [hd, hT]
        cases a
        · rw [hF]; exact hx
        · rw [hT]
      · have hd : endogenousDecision p lam x = false := by simp [endogenousDecision, hx]
        rw [hd, hF]
        cases a
        · rw [hF]
        · rw [hT]; linarith
    · rw [hT] at h0
      simp [endogenousDecision, h0]
  · -- monotone case
    intro hbl lam hlam
    have h1 : ∀ u, 0 < u → u ≤ 1 → p.b*u ≤ 2*p.ε + D*u^p.r := fun u h0 h1 => by
      have := le_trans hbl (s226w_le1 hε.le hD0 hr h0 h1); rwa [le_div_iff₀ h0] at this
    have h2 : ∀ s, 0 ≤ s → s < 1 → p.b*(1-s) ≤ 2*p.ε + D*(1 - s^p.r) := fun s h0 h1 => by
      have := le_trans hbl (s226w_le2 hε.le hD0 hr h0 h1)
      rwa [le_div_iff₀ (by linarith)] at this
    have hWm : Monotone W := fun x y hxy => by
      have := s226w_Phi_mono hε hr h1 h2 (hvle x y hxy)
      simp only [hWdef]; linarith
    have hcl : IsClosed (developmentSet p lam) := by
      rw [hset]; exact isClosed_le continuous_const hWc
    ext y; constructor
    · intro hy; exact csInf_le (hbdd lam) hy
    · intro hy
      have hm : developmentCutoff p lam ∈ developmentSet p lam :=
        hcl.csInf_mem (hne lam) (hbdd lam)
      rw [hset] at hm ⊢
      exact le_trans hm (hWm hy)
  · -- non-monotone case
    intro hbl
    obtain ⟨a', c', hac', hm1', hm2', hm3'⟩ := s226w_shape hε hD0 hr hbl
    have hinv : ∀ z, (t + 2*p.ε*z - t)/(2*p.ε) = z := fun z => by field_simp; ring
    set a := t + 2*p.ε*a' with hadef
    set c := t + 2*p.ε*c' with hcdef
    have hac : a < c := by nlinarith
    have hm1 : StrictMonoOn W (Iic a) := by
      intro x hx y hy hxy
      have := hm1' (show (x-t)/(2*p.ε) ∈ Iic a' by rw [← hinv a']; exact hvle _ _ hx)
        (show (y-t)/(2*p.ε) ∈ Iic a' by rw [← hinv a']; exact hvle _ _ hy) (hvlt x y hxy)
      simp only [hWdef]; linarith
    have hm2 : StrictAntiOn W (Icc a c) := by
      intro x hx y hy hxy
      have := hm2' (show (x-t)/(2*p.ε) ∈ Icc a' c' from
          ⟨by rw [← hinv a']; exact hvle _ _ hx.1, by rw [← hinv c']; exact hvle _ _ hx.2⟩)
        (show (y-t)/(2*p.ε) ∈ Icc a' c' from
          ⟨by rw [← hinv a']; exact hvle _ _ hy.1, by rw [← hinv c']; exact hvle _ _ hy.2⟩)
        (hvlt x y hxy)
      simp only [hWdef]; linarith
    have hm3 : StrictMonoOn W (Ici c) := by
      intro x hx y hy hxy
      have := hm3' (show (x-t)/(2*p.ε) ∈ Ici c' by rw [← hinv c']; exact hvle _ _ hx)
        (show (y-t)/(2*p.ε) ∈ Ici c' by rw [← hinv c']; exact hvle _ _ hy) (hvlt x y hxy)
      simp only [hWdef]; linarith
    set M := W a with hM
    set m := W c with hm
    have hmM : m < M := hm2 ⟨le_rfl, hac.le⟩ ⟨hac.le, le_rfl⟩ hac
    -- W ≤ M on Iic c, W ≥ m on Ici a
    have hleM : ∀ w, w ≤ c → W w ≤ M := by
      intro w hw
      rcases le_total w a with h | h
      · rcases eq_or_lt_of_le h with h' | h'
        · rw [h']
        · exact (hm1 (mem_Iic.2 h) (mem_Iic.2 le_rfl) h').le
      · rcases eq_or_lt_of_le h with h' | h'
        · rw [← h']
        · exact (hm2 ⟨le_rfl, hac.le⟩ ⟨h, hw⟩ h').le
    have hgem : ∀ w, a ≤ w → m ≤ W w := by
      intro w hw
      rcases le_total w c with h | h
      · rcases eq_or_lt_of_le h with h' | h'
        · rw [h']
        · exact (hm2 ⟨hw, h⟩ ⟨hac.le, le_rfl⟩ h').le
      · rcases eq_or_lt_of_le h with h' | h'
        · rw [← h']
        · exact (hm3 (mem_Ici.2 le_rfl) (mem_Ici.2 h) h').le
    -- IVT points
    have hleft : ∀ L, L ≤ M → ∃ x ≤ a, W x = L := by
      intro L hL
      set x0 := min a (L - K0 - (p.b + D)) with hx0
      have h0 : W x0 ≤ L := by linarith [hWhi x0, min_le_right a (L - K0 - (p.b + D))]
      obtain ⟨x, hx, hWx⟩ := intermediate_value_Icc (min_le_left a _) hWc.continuousOn ⟨h0, hL⟩
      exact ⟨x, hx.2, hWx⟩
    have hrightp : ∀ L, m ≤ L → ∃ z ≥ c, W z = L := by
      intro L hL
      set z0 := max c (L - K0 + (p.b + D)) with hz0
      have h0 : L ≤ W z0 := by linarith [hWlo z0, le_max_right c (L - K0 + (p.b + D))]
      obtain ⟨z, hz, hWz⟩ := intermediate_value_Icc (le_max_left c _) hWc.continuousOn ⟨hL, h0⟩
      exact ⟨z, hz.1, hWz⟩
    have hmid : ∀ L, m ≤ L → L ≤ M → ∃ y, a ≤ y ∧ y ≤ c ∧ W y = L := by
      intro L h1 h2
      obtain ⟨y, hy, hWy⟩ := intermediate_value_Icc' hac.le hWc.continuousOn ⟨h1, h2⟩
      exact ⟨y, hy.1, hy.2, hWy⟩
    refine ⟨-M, -m, by linarith, fun lam hlam => ?_⟩
    rcases lt_or_ge lam (-M) with hl | hl
    · -- only the right branch
      obtain ⟨z, hzc, hWz⟩ := hrightp (-lam) (by linarith)
      have hS : developmentSet p lam = Ici z := by
        rw [hset]; ext w; simp only [mem_setOf_eq, mem_Ici]; constructor
        · intro hw
          have hwc : c < w := by
            by_contra h; push_neg at h; linarith [hleM w h]
          by_contra h; push_neg at h
          have := hm3 (mem_Ici.2 hwc.le) (mem_Ici.2 hzc) h; linarith
        · intro hw
          rcases eq_or_lt_of_le hw with h | h
          · rw [← h, hWz]
          · have := hm3 (mem_Ici.2 hzc) (mem_Ici.2 (hzc.trans hw)) h; linarith
      have hx : z = developmentCutoff p lam := by
        unfold developmentCutoff; rw [hS, csInf_Ici]
      refine ⟨z, z, z, hx, le_rfl, le_rfl, fun _ => hS, fun h => ?_⟩
      exfalso; linarith [h.1]
    rcases le_or_gt lam (-m) with hl2 | hl2
    · -- middle
      obtain ⟨x, hxa, hWx⟩ := hleft (-lam) (by linarith)
      obtain ⟨y, hay, hyc, hWy⟩ := hmid (-lam) (by linarith) (by linarith)
      obtain ⟨z, hzc, hWz⟩ := hrightp (-lam) (by linarith)
      have hS : developmentSet p lam = Icc x y ∪ Ici z := by
        rw [hset]; ext w; simp only [mem_setOf_eq, mem_union, mem_Icc, mem_Ici]; constructor
        · intro hw
          rcases le_total w a with h | h
          · left; refine ⟨?_, by linarith⟩
            by_contra h'; push_neg at h'
            have := hm1 (mem_Iic.2 h) (mem_Iic.2 hxa) h'; linarith
          rcases le_total w c with h' | h'
          · left; refine ⟨by linarith, ?_⟩
            by_contra h''; push_neg at h''
            have := hm2 ⟨hay, hyc⟩ ⟨h, h'⟩ h''; linarith
          · right
            by_contra h''; push_neg at h''
            have := hm3 (mem_Ici.2 h') (mem_Ici.2 hzc) h''; linarith
        · rintro (⟨h1, h2⟩ | h)
          · rcases le_total w a with h | h
            · rcases eq_or_lt_of_le h1 with h' | h'
              · rw [← h', hWx]
              · have := hm1 (mem_Iic.2 hxa) (mem_Iic.2 h) h'; linarith
            · rcases eq_or_lt_of_le h2 with h' | h'
              · rw [h', hWy]
              · have := hm2 ⟨h, h2.trans hyc⟩ ⟨hay, hyc⟩ h'; linarith
          · rcases eq_or_lt_of_le h with h' | h'
            · rw [← h', hWz]
            · have := hm3 (mem_Ici.2 hzc) (mem_Ici.2 (hzc.trans h)) h'; linarith
      have hxS : x ∈ developmentSet p lam := by
        rw [hS]; left; exact ⟨le_rfl, by linarith⟩
      have hlow : ∀ w ∈ developmentSet p lam, x ≤ w := by
        intro w hw; rw [hS] at hw
        rcases hw with ⟨h1, _⟩ | h
        · exact h1
        · have : x ≤ z := by linarith
          exact le_trans this h
      have hx : x = developmentCutoff p lam := by
        unfold developmentCutoff; exact (IsLeast.csInf_eq ⟨hxS, hlow⟩).symm
      refine ⟨x, y, z, hx, by linarith, by linarith, fun h => ?_, fun _ => hS⟩
      exfalso; rcases h with h | h <;> linarith
    · -- only the left branch
      obtain ⟨x, hxa, hWx⟩ := hleft (-lam) (by linarith)
      have hS : developmentSet p lam = Ici x := by
        rw [hset]; ext w; simp only [mem_setOf_eq, mem_Ici]; constructor
        · intro hw
          by_contra h; push_neg at h
          have := hm1 (mem_Iic.2 (h.le.trans hxa)) (mem_Iic.2 hxa) h; linarith
        · intro hw
          rcases le_total w a with h | h
          · rcases eq_or_lt_of_le hw with h' | h'
            · rw [← h', hWx]
            · have := hm1 (mem_Iic.2 hxa) (mem_Iic.2 h) h'; linarith
          · linarith [hgem w h]
      have hx : x = developmentCutoff p lam := by
        unfold developmentCutoff; rw [hS, csInf_Ici]
      refine ⟨x, x, x, hx, le_rfl, le_rfl, fun _ => hS, fun h => ?_⟩
      exfalso; linarith [h.2]
