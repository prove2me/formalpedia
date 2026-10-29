-- Prove2me | solution 1 for WangGreenTech.Regulation.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T05:59:10.698809+00:00
-- url     : https://prove2.me/submissions/b8d89fdb-2d5f-4adb-97d3-eb8e2a0c562c

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

theorem solution (p : Model) (hp : p.Valid) :
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
