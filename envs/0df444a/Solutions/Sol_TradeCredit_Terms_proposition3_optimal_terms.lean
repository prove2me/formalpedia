-- Prove2me | solution 1 for TradeCredit.Terms.proposition3_optimal_terms
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T09:41:23.940199+00:00
-- url     : https://prove2.me/submissions/c42c26d0-5e20-457a-988c-d1c05e99dec6

import Mathlib
import Definitions.Def_TradeCredit_Terms_Model
import Theorems.Thm_TradeCredit_Terms_proposition3_two_part_low_cash

namespace TradeCredit.Terms
namespace Aux

open MeasureTheory intervalIntegral Set

variable {f : ℝ → ℝ}

lemma f_nonneg (hf : DemandModel f) (x : ℝ) : 0 ≤ f x := by
  rcases lt_or_ge x 0 with h | h
  · rw [hf.zero_of_neg x h]
  · exact (hf.pos x h).le

lemma f_integrable (hf : DemandModel f) : Integrable f := by
  have h1 : IntegrableOn f (Iio 0) := by
    have : EqOn f 0 (Iio 0) := fun x hx => hf.zero_of_neg x hx
    exact (integrableOn_zero).congr_fun this.symm measurableSet_Iio
  have : (Set.univ : Set ℝ) = Iio 0 ∪ Ici 0 := by ext x; simp
  rw [← integrableOn_univ, this]
  exact h1.union hf.integrableOn

lemma f_ii (hf : DemandModel f) (a b : ℝ) : IntervalIntegrable f volume a b :=
  (f_integrable hf).intervalIntegrable

lemma F_cont (hf : DemandModel f) : Continuous (F f) := by
  unfold F
  exact intervalIntegral.continuous_primitive (f_ii hf) 0

lemma Fbar_cont (hf : DemandModel f) : Continuous (Fbar f) := by
  unfold Fbar; exact continuous_const.sub (F_cont hf)

lemma F_sub (hf : DemandModel f) (a b : ℝ) : F f b - F f a = ∫ x in a..b, f x := by
  unfold F
  rw [sub_eq_iff_eq_add', intervalIntegral.integral_add_adjacent_intervals (f_ii hf 0 a) (f_ii hf a b)]

lemma F_zero : F f 0 = 0 := by simp [F]

lemma Fbar_zero : Fbar f 0 = 1 := by simp [Fbar, F]

lemma F_mono (hf : DemandModel f) {a b : ℝ} (hab : a ≤ b) : F f a ≤ F f b := by
  have := F_sub hf a b
  have h2 : 0 ≤ ∫ x in a..b, f x := intervalIntegral.integral_nonneg hab (fun x _ => f_nonneg hf x)
  linarith

lemma F_nonneg (hf : DemandModel f) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ F f x := by
  have := F_mono hf hx; rwa [F_zero] at this

lemma F_strictMono (hf : DemandModel f) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) : F f a < F f b := by
  have := F_sub hf a b
  have h2 : 0 < ∫ x in a..b, f x := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on (f_ii hf a b)
    · intro x hx; exact hf.pos x (by linarith [hx.1])
    · exact hab
  linarith

/-- `F̄(x) = ∫_{x}^∞ f`. -/
lemma Fbar_eq (hf : DemandModel f) {x : ℝ} (hx : 0 ≤ x) : Fbar f x = ∫ t in Ioi x, f t := by
  have h := hf.total
  have hsplit : Ici (0:ℝ) = Ico 0 x ∪ Ici x := (Set.Ico_union_Ici_eq_Ici hx).symm
  have hI : ∫ t in Ici 0, f t = (∫ t in Ico 0 x, f t) + ∫ t in Ici x, f t := by
    rw [hsplit]
    apply setIntegral_union
    · exact Set.disjoint_left.mpr (fun a ha hb => by simp at ha hb; linarith [ha.2, hb])
    · exact measurableSet_Ici
    · exact (f_integrable hf).integrableOn
    · exact (f_integrable hf).integrableOn
  have h1 : ∫ t in Ico 0 x, f t = F f x := by
    unfold F
    rw [intervalIntegral.integral_of_le hx, integral_Ico_eq_integral_Ioc]
  have h2 : ∫ t in Ici x, f t = ∫ t in Ioi x, f t := integral_Ici_eq_integral_Ioi
  unfold Fbar; linarith

lemma Fbar_pos (hf : DemandModel f) {x : ℝ} (hx : 0 ≤ x) : 0 < Fbar f x := by
  have h1 := F_strictMono hf hx (lt_add_one x)
  have h2 : Fbar f (x+1) = ∫ t in Ioi (x+1), f t := Fbar_eq hf (by linarith)
  have h3 : 0 ≤ ∫ t in Ioi (x+1), f t := setIntegral_nonneg measurableSet_Ioi (fun t _ => f_nonneg hf t)
  unfold Fbar at *; linarith

lemma Fbar_le_one (hf : DemandModel f) {x : ℝ} (hx : 0 ≤ x) : Fbar f x ≤ 1 := by
  have := F_nonneg hf hx; unfold Fbar; linarith

lemma Fbar_lt_one (hf : DemandModel f) {x : ℝ} (hx : 0 < x) : Fbar f x < 1 := by
  have := F_strictMono hf le_rfl hx; rw [F_zero] at this; unfold Fbar; linarith

lemma Fbar_anti (hf : DemandModel f) {a b : ℝ} (hab : a ≤ b) : Fbar f b ≤ Fbar f a := by
  have := F_mono hf hab; unfold Fbar; linarith

lemma Fbar_strictAnti (hf : DemandModel f) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    Fbar f b < Fbar f a := by
  have := F_strictMono hf ha hab; unfold Fbar; linarith

/-! failure rate -/

lemma h_pos (hf : DemandModel f) {x : ℝ} (hx : 0 ≤ x) : 0 < failureRate f x :=
  div_pos (hf.pos x hx) (Fbar_pos hf hx)

lemma h_mono (hf : DemandModel f) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    failureRate f a ≤ failureRate f b :=
  hf.ifr (mem_Ici.mpr ha) (mem_Ici.mpr (ha.trans hab)) hab

lemma f_eq (hf : DemandModel f) {x : ℝ} (hx : 0 ≤ x) : f x = failureRate f x * Fbar f x := by
  unfold failureRate; field_simp [(Fbar_pos hf hx).ne']

lemma h_zero (hf : DemandModel f) : failureRate f 0 = f 0 := by
  simp [failureRate, Fbar_zero]

lemma g_zero : genFailureRate f 0 = 0 := by simp [genFailureRate]

lemma g_nonneg (hf : DemandModel f) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ genFailureRate f x :=
  mul_nonneg hx (h_pos hf hx).le

lemma g_strictMono (hf : DemandModel f) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    genFailureRate f a < genFailureRate f b := by
  unfold genFailureRate
  have h1 := h_mono hf ha hab.le
  have h2 := h_pos hf ha
  have h3 := h_pos hf (ha.trans hab.le)
  calc a * failureRate f a ≤ a * failureRate f b := mul_le_mul_of_nonneg_left h1 ha
    _ < b * failureRate f b := mul_lt_mul_of_pos_right hab h3

lemma g_mono (hf : DemandModel f) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    genFailureRate f a ≤ genFailureRate f b := by
  rcases hab.lt_or_eq with h | h
  · exact (g_strictMono hf ha h).le
  · rw [h]

lemma g_ge (hf : DemandModel f) {x : ℝ} (hx : 0 ≤ x) : x * f 0 ≤ genFailureRate f x := by
  unfold genFailureRate
  rw [← h_zero hf]
  exact mul_le_mul_of_nonneg_left (h_mono hf le_rfl hx) hx

lemma f_contAt (hf : DemandModel f) {x : ℝ} (hx : 0 < x) : ContinuousAt f x :=
  hf.continuousOn.continuousAt (Ici_mem_nhds hx)

lemma g_contAt (hf : DemandModel f) {x : ℝ} (hx : 0 < x) : ContinuousAt (genFailureRate f) x := by
  unfold genFailureRate failureRate
  exact continuousAt_id.mul ((f_contAt hf hx).div (Fbar_cont hf).continuousAt
    (Fbar_pos hf hx.le).ne')

/-- local bounds on `f` near a point of `[0, ∞)`. -/
lemma f_near (hf : DemandModel f) (x : ℝ) (hx : 0 ≤ x) :
    ∃ δ > 0, ∀ y, 0 ≤ y → |y - x| ≤ δ → f x / 2 ≤ f y ∧ f y ≤ 2 * f x := by
  have hc := hf.continuousOn x (mem_Ici.mpr hx)
  have hpos := hf.pos x hx
  rw [Metric.continuousWithinAt_iff] at hc
  obtain ⟨δ, hδ, h⟩ := hc (f x / 2) (by linarith)
  refine ⟨δ / 2, by linarith, fun y hy hyx => ?_⟩
  have := h (mem_Ici.mpr hy) (by rw [Real.dist_eq]; linarith)
  rw [Real.dist_eq, abs_lt] at this
  constructor <;> linarith [this.1, this.2]


lemma F_diff_le (hf : DemandModel f) {a b M : ℝ} (hab : a ≤ b) (h : ∀ x ∈ Icc a b, f x ≤ M) :
    F f b - F f a ≤ M * (b - a) := by
  rw [F_sub hf]
  have := intervalIntegral.integral_mono_on hab (f_ii hf a b) intervalIntegrable_const h
  simpa [mul_comm] using this

lemma F_diff_ge (hf : DemandModel f) {a b M : ℝ} (hab : a ≤ b) (h : ∀ x ∈ Icc a b, M ≤ f x) :
    M * (b - a) ≤ F f b - F f a := by
  rw [F_sub hf]
  have := intervalIntegral.integral_mono_on hab intervalIntegrable_const (f_ii hf a b) h
  simpa [mul_comm] using this

/-! `g⁻¹(1)` -/

lemma S_bdd (hf : DemandModel f) : BddAbove {q : ℝ | 0 ≤ q ∧ genFailureRate f q ≤ 1} := by
  refine ⟨1 / f 0, fun q hq => ?_⟩
  have h0 := hf.pos 0 le_rfl
  have := g_ge hf hq.1
  rw [le_div_iff₀ h0]; linarith [hq.2]

lemma exists_pos_small (hf : DemandModel f) : ∃ q, 0 < q ∧ genFailureRate f q ≤ 1 := by
  obtain ⟨δ, hδ, hb⟩ := f_near hf 0 le_rfl
  have h0 := hf.pos 0 le_rfl
  set q := min δ (1 / (8 * f 0)) with hq
  have hqpos : 0 < q := lt_min hδ (by positivity)
  have hqδ : q ≤ δ := min_le_left _ _
  have hq8 : q ≤ 1 / (8 * f 0) := min_le_right _ _
  have hq8' : q * (8 * f 0) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at hq8
  refine ⟨q, hqpos, ?_⟩
  have hFq : F f q - F f 0 ≤ (2 * f 0) * (q - 0) :=
    F_diff_le hf hqpos.le (fun x hx => (hb x hx.1 (by rw [sub_zero, abs_of_nonneg hx.1]; linarith [hx.2])).2)
  rw [F_zero] at hFq
  have hFbar : 3/4 ≤ Fbar f q := by unfold Fbar; nlinarith
  have hfq : f q ≤ 2 * f 0 := (hb q hqpos.le (by rw [abs_of_nonneg (by linarith)]; linarith)).2
  unfold genFailureRate failureRate
  rw [mul_div_assoc', div_le_one (by linarith)]
  nlinarith

lemma m_pos (hf : DemandModel f) : 0 < gInv1 f := by
  obtain ⟨q, hq, hg⟩ := exists_pos_small hf
  exact lt_of_lt_of_le hq (le_csSup (S_bdd hf) ⟨hq.le, hg⟩)

lemma g_lt_one (hf : DemandModel f) {x : ℝ} (hx : 0 ≤ x) (hxm : x < gInv1 f) :
    genFailureRate f x < 1 := by
  obtain ⟨s, hs, hxs⟩ := exists_lt_of_lt_csSup (⟨0, le_rfl, by rw [g_zero]; norm_num⟩ :
    ({q : ℝ | 0 ≤ q ∧ genFailureRate f q ≤ 1}).Nonempty) hxm
  exact lt_of_lt_of_le (g_strictMono hf hx hxs) hs.2

lemma g_m_le (hf : DemandModel f) : genFailureRate f (gInv1 f) ≤ 1 := by
  by_contra h
  push Not at h
  have hm := m_pos hf
  have hc := g_contAt hf hm
  have hev : ∀ᶠ y in nhds (gInv1 f), 1 < genFailureRate f y := hc.eventually (lt_mem_nhds h)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨s, hs, hxs⟩ := exists_lt_of_lt_csSup (⟨0, le_rfl, by rw [g_zero]; norm_num⟩ :
    ({q : ℝ | 0 ≤ q ∧ genFailureRate f q ≤ 1}).Nonempty) (show gInv1 f - ε < gInv1 f by linarith)
  have hsm : s ≤ gInv1 f := le_csSup (S_bdd hf) hs
  have := hball (show dist s (gInv1 f) < ε by
    rw [Real.dist_eq, abs_of_nonpos (by linarith)]; linarith)
  linarith [hs.2]

lemma Mstar_pos (hf : DemandModel f) : 0 < Mstar f :=
  mul_pos (m_pos hf) (Fbar_pos hf (m_pos hf).le)

/-! `φ(q) = q F̄(q)` -/

lemma F_hasDerivAt (hf : DemandModel f) {x : ℝ} (hx : 0 < x) : HasDerivAt (F f) (f x) x := by
  unfold F
  apply intervalIntegral.integral_hasDerivAt_right (f_ii hf 0 x)
  · exact (hf.continuousOn.mono Ioi_subset_Ici_self).stronglyMeasurableAtFilter isOpen_Ioi x hx
  · exact f_contAt hf hx

lemma phi_strictMono (hf : DemandModel f) :
    StrictMonoOn (fun q => q * Fbar f q) (Icc 0 (gInv1 f)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
  · exact (continuous_id.mul (Fbar_cont hf)).continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    have hd : HasDerivAt (fun q => q * Fbar f q) (1 * Fbar f x + x * (- f x)) x := by
      apply (hasDerivAt_id x).mul
      unfold Fbar
      simpa using (F_hasDerivAt hf hx.1).const_sub 1
    rw [hd.deriv]
    have hg := g_lt_one hf hx.1.le hx.2
    have hfe := f_eq hf hx.1.le
    have hFp := Fbar_pos hf hx.1.le
    unfold genFailureRate at hg
    rw [hfe]
    nlinarith [mul_pos hFp (sub_pos.mpr hg)]

/-- smallest root -/
noncomputable def Qv (f : ℝ → ℝ) (V : ℝ) : ℝ := sInf {q : ℝ | 0 ≤ q ∧ q * Fbar f q = V}

lemma Qv_spec (hf : DemandModel f) {V : ℝ} (hV0 : 0 ≤ V) (hVM : V ≤ Mstar f) :
    0 ≤ Qv f V ∧ Qv f V ≤ gInv1 f ∧ Qv f V * Fbar f (Qv f V) = V := by
  have hm := m_pos hf
  have hivt := intermediate_value_Icc hm.le
    ((continuous_id.mul (Fbar_cont hf)).continuousOn (s := Icc 0 (gInv1 f)))
  have hV : V ∈ Icc ((fun q => q * Fbar f q) 0) ((fun q => q * Fbar f q) (gInv1 f)) := by
    exact ⟨by simpa using hV0, by simpa [Mstar] using hVM⟩
  obtain ⟨q0, hq0, hq0V⟩ := hivt hV
  simp only [Pi.mul_apply, id] at hq0V
  have hleast : IsLeast {q : ℝ | 0 ≤ q ∧ q * Fbar f q = V} q0 := by
    refine ⟨⟨hq0.1, hq0V⟩, fun q hq => ?_⟩
    by_contra hlt
    push Not at hlt
    have := phi_strictMono hf ⟨hq.1, by linarith [hq0.2]⟩ hq0 hlt
    simp only at this
    linarith [hq.2]
  have : Qv f V = q0 := hleast.csInf_eq
  rw [this]; exact ⟨hq0.1, hq0.2, hq0V⟩

lemma Qv_mono (hf : DemandModel f) {V₁ V₂ : ℝ} (h1 : 0 ≤ V₁) (h12 : V₁ ≤ V₂) (h2 : V₂ ≤ Mstar f) :
    Qv f V₁ ≤ Qv f V₂ := by
  obtain ⟨a1, b1, c1⟩ := Qv_spec hf h1 (h12.trans h2)
  obtain ⟨a2, b2, c2⟩ := Qv_spec hf (h1.trans h12) h2
  by_contra hlt
  push Not at hlt
  have := phi_strictMono hf ⟨a2, b2⟩ ⟨a1, b1⟩ hlt
  simp only at this
  linarith

lemma Qv_gap (hf : DemandModel f) {V₁ V₂ : ℝ} (h1 : 0 ≤ V₁) (h12 : V₁ ≤ V₂) (h2 : V₂ ≤ Mstar f) :
    V₂ - V₁ ≤ Qv f V₂ - Qv f V₁ := by
  have hmono := Qv_mono hf h1 h12 h2
  obtain ⟨a1, b1, c1⟩ := Qv_spec hf h1 (h12.trans h2)
  obtain ⟨a2, b2, c2⟩ := Qv_spec hf (h1.trans h12) h2
  have e1 := Fbar_le_one hf a2
  have e2 := Fbar_anti hf hmono
  nlinarith [mul_nonneg a1 (sub_nonneg.mpr e2), mul_nonneg (sub_nonneg.mpr hmono) (sub_nonneg.mpr e1)]

lemma Qfun_eq (αb K θb θt : ℝ) :
    Qfun f αb K θb θt = Qv f ((θt + Cfun f αb K θb) * Fbar f θt) := rfl

/-! The bank kernel and `C`. -/

lemma Fhatb_zero (αb : ℝ) : Fhatb f αb 0 = 1 := by simp [Fhatb, Fbar_zero, g_zero]

lemma Cfun_zero (αb K : ℝ) : Cfun f αb K 0 = K := by simp [Cfun, Fhatb_zero]

lemma w_pos_of (hf : DemandModel f) {αb θ : ℝ} (hθ : 0 ≤ θ) (h : 0 < Fhatb f αb θ) :
    0 < 1 - αb * genFailureRate f θ := by
  unfold Fhatb at h
  exact pos_of_mul_pos_right h (Fbar_pos hf hθ).le

lemma Fhatb_anti (hf : DemandModel f) {αb θ x y : ℝ} (hαb : 0 ≤ αb) (hθ : 0 < Fhatb f αb θ)
    (hx : 0 ≤ x) (hxy : x ≤ y) (hyθ : y ≤ θ) : Fhatb f αb y ≤ Fhatb f αb x := by
  have hw := w_pos_of hf (hx.trans (hxy.trans hyθ)) hθ
  have hgy : genFailureRate f y ≤ genFailureRate f θ := g_mono hf (hx.trans hxy) hyθ
  have hgx : genFailureRate f x ≤ genFailureRate f y := g_mono hf hx hxy
  have hwy : 0 < 1 - αb * genFailureRate f y := by nlinarith
  unfold Fhatb
  apply mul_le_mul (Fbar_anti hf hxy) (by nlinarith) hwy.le (Fbar_pos hf hx).le

lemma Fhatb_strictAnti (hf : DemandModel f) {αb θ x y : ℝ} (hαb : 0 ≤ αb) (hθ : 0 < Fhatb f αb θ)
    (hx : 0 ≤ x) (hxy : x < y) (hyθ : y ≤ θ) : Fhatb f αb y < Fhatb f αb x := by
  have hgy : genFailureRate f y ≤ genFailureRate f θ := g_mono hf (hx.trans hxy.le) hyθ
  have hgx : genFailureRate f x ≤ genFailureRate f y := g_mono hf hx hxy.le
  have hw := w_pos_of hf (hx.trans (hxy.le.trans hyθ)) hθ
  have hwy : 0 < 1 - αb * genFailureRate f y := by nlinarith
  have h1 := Fbar_strictAnti hf hx hxy
  unfold Fhatb
  calc Fbar f y * (1 - αb * genFailureRate f y) < Fbar f x * (1 - αb * genFailureRate f y) :=
        mul_lt_mul_of_pos_right h1 hwy
    _ ≤ Fbar f x * (1 - αb * genFailureRate f x) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (Fbar_pos hf hx).le

lemma Fhatb_le_Fbar (hf : DemandModel f) {αb x : ℝ} (hαb : 0 ≤ αb) (hx : 0 ≤ x) :
    Fhatb f αb x ≤ Fbar f x := by
  unfold Fhatb
  have := g_nonneg hf hx
  have := Fbar_pos hf hx
  nlinarith [mul_nonneg hαb (g_nonneg hf hx)]

lemma Fhatb_le_one (hf : DemandModel f) {αb x : ℝ} (hαb : 0 ≤ αb) (hx : 0 ≤ x) :
    Fhatb f αb x ≤ 1 := (Fhatb_le_Fbar hf hαb hx).trans (Fbar_le_one hf hx)

lemma Fhatb_ii (hf : DemandModel f) {αb θ a b : ℝ} (hαb : 0 ≤ αb) (hθ : 0 < Fhatb f αb θ)
    (ha : 0 ≤ a) (hab : a ≤ b) (hbθ : b ≤ θ) : IntervalIntegrable (Fhatb f αb) volume a b := by
  apply AntitoneOn.intervalIntegrable
  rw [uIcc_of_le hab]
  intro x hx y hy hxy
  exact Fhatb_anti hf hαb hθ (ha.trans hx.1) hxy (hy.2.trans hbθ)

/-- `C(θ) ≥ K + K (1 - F̂_b(θ))`. -/
lemma C_ge (hf : DemandModel f) {αb K θ : ℝ} (hαb : 0 ≤ αb) (hK : 0 < K) (hθ0 : 0 ≤ θ)
    (hθ : 0 < Fhatb f αb θ) : K + K * (1 - Fhatb f αb θ) ≤ Cfun f αb K θ := by
  have hint : θ * Fhatb f αb θ ≤ ∫ x in (0)..θ, Fhatb f αb x := by
    have := intervalIntegral.integral_mono_on hθ0 intervalIntegrable_const
      (Fhatb_ii hf hαb hθ le_rfl hθ0 le_rfl)
      (fun x hx => Fhatb_anti hf hαb hθ hx.1 hx.2 le_rfl)
    simpa [mul_comm] using this
  have h1 := Fhatb_le_one hf hαb hθ0
  unfold Cfun
  rw [le_sub_iff_add_le, le_div_iff₀ hθ]
  nlinarith [mul_nonneg hK.le (sq_nonneg (1 - Fhatb f αb θ))]

lemma C_ge_K (hf : DemandModel f) {αb K θ : ℝ} (hαb : 0 ≤ αb) (hK : 0 < K) (hθ0 : 0 ≤ θ)
    (hθ : 0 < Fhatb f αb θ) : K ≤ Cfun f αb K θ := by
  have := C_ge hf hαb hK hθ0 hθ
  have := Fhatb_le_one hf hαb hθ0
  nlinarith

/-- `C(θ) - C(θ') ≥ K (F̂_b(θ') - F̂_b(θ))` for `0 ≤ θ' ≤ θ`. -/
lemma C_diff (hf : DemandModel f) {αb K θ θ' : ℝ} (hαb : 0 ≤ αb) (hK : 0 < K) (h0 : 0 ≤ θ')
    (h1 : θ' ≤ θ) (hθ : 0 < Fhatb f αb θ) :
    K * (Fhatb f αb θ' - Fhatb f αb θ) ≤ Cfun f αb K θ - Cfun f αb K θ' := by
  have hθ' : Fhatb f αb θ ≤ Fhatb f αb θ' := Fhatb_anti hf hαb hθ h0 h1 le_rfl
  have hθ'pos : 0 < Fhatb f αb θ' := lt_of_lt_of_le hθ hθ'
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (Fhatb_ii hf hαb hθ le_rfl h0 h1) (Fhatb_ii hf hαb hθ h0 h1 le_rfl)
  have hint : (θ - θ') * Fhatb f αb θ ≤ ∫ x in θ'..θ, Fhatb f αb x := by
    have := intervalIntegral.integral_mono_on h1 intervalIntegrable_const
      (Fhatb_ii hf hαb hθ h0 h1 le_rfl)
      (fun x hx => Fhatb_anti hf hαb hθ (h0.trans hx.1) hx.2 le_rfl)
    simpa [mul_comm] using this
  have hN : K ≤ K + ∫ x in (0)..θ', Fhatb f αb x := by
    have : 0 ≤ ∫ x in (0)..θ', Fhatb f αb x := intervalIntegral.integral_nonneg h0 (fun x hx => (lt_of_lt_of_le hθ
      (Fhatb_anti hf hαb hθ hx.1 (hx.2.trans h1) le_rfl)).le)
    linarith
  have hle1 := Fhatb_le_one hf hαb h0
  set N := K + ∫ x in (0)..θ', Fhatb f αb x with hNdef
  set a := Fhatb f αb θ
  set b := Fhatb f αb θ'
  have key : Cfun f αb K θ ≥ N / a - θ' := by
    unfold Cfun
    rw [← hsplit]
    have : (N + (θ - θ') * a) / a ≤
        (K + ((∫ x in (0)..θ', Fhatb f αb x) + ∫ x in θ'..θ, Fhatb f αb x)) / a := by
      apply div_le_div_of_nonneg_right _ hθ.le
      rw [hNdef]; linarith
    have e : (N + (θ - θ') * a) / a = N / a + (θ - θ') := by field_simp
    rw [e] at this
    show N / a - θ' ≤ _
    linarith
  have hC' : Cfun f αb K θ' = N / b - θ' := rfl
  rw [hC']
  have : N / a - N / b = N * (b - a) / (a * b) := by field_simp
  have h2 : K * (b - a) ≤ N * (b - a) / (a * b) := by
    rw [le_div_iff₀ (mul_pos hθ hθ'pos)]
    have hab1 : a * b ≤ 1 := by nlinarith
    have hba : 0 ≤ b - a := by linarith
    nlinarith [mul_nonneg hK.le hba, mul_nonneg (mul_nonneg hK.le hba) (sub_nonneg.mpr hab1),
      mul_nonneg (sub_nonneg.mpr hN) hba]
  linarith

/-! Theta -/

lemma mem_Theta_Fhatb_pos (hf : DemandModel f) {c αb K θb θt : ℝ} (hc : 0 < c)
    (h : (θb, θt) ∈ Theta f c αb K) : 0 < Fhatb f αb θb := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  simp only at h0 h1 h2 h3 h4
  unfold wc wt at h4
  have hQ : 0 ≤ Qfun f αb K θb θt := Real.sInf_nonneg (fun q hq => hq.1)
  have hr : 0 < Fbar f (Qfun f αb K θb θt) / Fbar f θt :=
    div_pos (Fbar_pos hf hQ) (Fbar_pos hf (h0.trans h1))
  by_contra hn
  push Not at hn
  have : Fhatb f αb θb * (Fbar f (Qfun f αb K θb θt) / Fbar f θt) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hn hr.le
  linarith

lemma mem_Theta_facts (hf : DemandModel f) {c αb K θb θt : ℝ} (hc : 0 < c) (hαb : 0 ≤ αb)
    (hK : 0 < K) (h : (θb, θt) ∈ Theta f c αb K) :
    0 < Fhatb f αb θb ∧ K ≤ Cfun f αb K θb ∧ 0 ≤ (θt + Cfun f αb K θb) * Fbar f θt ∧
      θt ≤ gInv1 f := by
  have hF := mem_Theta_Fhatb_pos hf hc h
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  simp only at h0 h1 h2 h3 h4
  have hC := C_ge_K hf hαb hK h0 hF
  have hV : 0 ≤ (θt + Cfun f αb K θb) * Fbar f θt :=
    mul_nonneg (by linarith) (Fbar_pos hf (h0.trans h1)).le
  refine ⟨hF, hC, hV, ?_⟩
  obtain ⟨_, hb, _⟩ := Qv_spec hf hV h2
  rw [Qfun_eq] at h3
  linarith

/-- Lowering `θ_b` keeps the contract in `Θ` and lowers `Q` by at least the drop in the
right-hand side. -/
lemma shift (hf : DemandModel f) {c αb K θb θt θ' : ℝ} (hc : 0 < c) (hαb : 0 ≤ αb)
    (hK : 0 < K) (h : (θb, θt) ∈ Theta f c αb K) (h0 : 0 ≤ θ') (h1 : θ' ≤ θb) :
    (θ', θt) ∈ Theta f c αb K ∧
      (Cfun f αb K θb - Cfun f αb K θ') * Fbar f θt ≤ Qfun f αb K θb θt - Qfun f αb K θ' θt := by
  obtain ⟨hF, hC, hV, htm⟩ := mem_Theta_facts hf hc hαb hK h
  have hmem := h
  obtain ⟨g0, g1, g2, g3, g4⟩ := h
  simp only at g0 g1 g2 g3 g4
  have hFt := Fbar_pos hf (g0.trans g1)
  have hCd := C_diff hf hαb hK h0 h1 hF
  have hF' : Fhatb f αb θb ≤ Fhatb f αb θ' := Fhatb_anti hf hαb hF h0 h1 le_rfl
  have hC' := C_ge_K hf hαb hK h0 (lt_of_lt_of_le hF hF')
  have hCC : Cfun f αb K θ' ≤ Cfun f αb K θb := by nlinarith
  set V := (θt + Cfun f αb K θb) * Fbar f θt
  set V' := (θt + Cfun f αb K θ') * Fbar f θt with hV'def
  have hV'0 : 0 ≤ V' := mul_nonneg (by linarith) hFt.le
  have hVV : V' ≤ V := mul_le_mul_of_nonneg_right (by linarith) hFt.le
  have hgap := Qv_gap hf hV'0 hVV g2
  have hQQ := Qv_mono hf hV'0 hVV g2
  obtain ⟨q0, qm, qV⟩ := Qv_spec hf hV'0 (hVV.trans g2)
  refine ⟨⟨h0, h1.trans g1, hVV.trans g2, ?_, ?_⟩, ?_⟩
  · show θt ≤ Qv f V'
    by_contra hlt
    push Not at hlt
    have := phi_strictMono hf ⟨q0, qm⟩ ⟨g0.trans g1, htm⟩ hlt
    simp only at this
    rw [qV, hV'def] at this
    nlinarith [mul_pos (lt_of_lt_of_le hK hC') hFt]
  · show c ≤ Fhatb f αb θ' * (Fbar f (Qv f V') / Fbar f θt)
    have g4' : c ≤ Fhatb f αb θb * (Fbar f (Qv f V) / Fbar f θt) := g4
    have hQ0 : 0 ≤ Qv f V := (Qv_spec hf hV g2).1
    have e1 : Fbar f (Qv f V) ≤ Fbar f (Qv f V') := Fbar_anti hf hQQ
    have e2 : Fbar f (Qv f V) / Fbar f θt ≤ Fbar f (Qv f V') / Fbar f θt :=
      div_le_div_of_nonneg_right e1 hFt.le
    calc c ≤ _ := g4'
      _ ≤ _ := mul_le_mul hF' e2 (div_pos (Fbar_pos hf hQ0) hFt).le (hF.trans_le hF').le
  · rw [Qfun_eq, Qfun_eq]
    have : V - V' = (Cfun f αb K θb - Cfun f αb K θ') * Fbar f θt := by
      simp only [V, V']; ring
    linarith

/-- the profit difference -/
lemma PiS_diff (c αb αt K θb θt θ' : ℝ) :
    PiS f c αb αt K θ' θt - PiS f c αb αt K θb θt =
      c * (Qfun f αb K θb θt - Qfun f αb K θ' θt) +
      αb * ((∫ x in (0)..θb, x * f x) - ∫ x in (0)..θ', x * f x) +
      αt * ((∫ x in θb..θt, (x - θb) * f x) - ∫ x in θ'..θt, (x - θ') * f x) := by
  unfold PiS; ring

lemma xf_ii (hf : DemandModel f) (a b r : ℝ) :
    IntervalIntegrable (fun x => (x - r) * f x) volume a b :=
  (f_ii hf a b).continuousOn_mul ((continuous_id.sub continuous_const).continuousOn)

lemma xf_ii' (hf : DemandModel f) (a b : ℝ) :
    IntervalIntegrable (fun x => x * f x) volume a b :=
  (f_ii hf a b).continuousOn_mul (continuous_id.continuousOn)

lemma opt_le {c αb αt K θb θt θ' : ℝ} (hopt : IsOptimalContract f c αb αt K θb θt)
    (hmem : (θ', θt) ∈ Theta f c αb K) : PiS f c αb αt K θ' θt ≤ PiS f c αb αt K θb θt :=
  hopt.2 hmem

lemma int_xf_nonneg (hf : DemandModel f) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    0 ≤ ∫ x in a..b, x * f x :=
  intervalIntegral.integral_nonneg hab (fun x hx => mul_nonneg (ha.trans hx.1) (f_nonneg hf x))

/-- Part 2 of Proposition 3. -/
theorem part_net_alpha0 (hf : DemandModel f) {c αb αt : ℝ} (hc0 : 0 < c) (hαb0 : 0 ≤ αb)
    (hαt : αt = 0) {K : ℝ} (hK : 0 < K) {θb θt : ℝ}
    (hopt : IsOptimalContract f c αb αt K θb θt) : θb = 0 ∧ dt f αb θb = 0 := by
  subst hαt
  have hb0 : θb = 0 := by
    have hθb0 : 0 ≤ θb := hopt.1.1
    by_contra hne
    have hpos : 0 < θb := lt_of_le_of_ne hθb0 (Ne.symm hne)
    obtain ⟨hmem, hgap⟩ := shift hf hc0 hαb0 hK hopt.1 le_rfl hθb0
    have hle := opt_le hopt hmem
    have hd := PiS_diff (f := f) c αb 0 K θb θt 0
    have hF := mem_Theta_Fhatb_pos hf hc0 hopt.1
    have hstrict := Fhatb_strictAnti hf hαb0 hF le_rfl hpos le_rfl
    rw [Fhatb_zero] at hstrict
    have hCd := C_diff hf hαb0 hK le_rfl hθb0 hF
    rw [Fhatb_zero] at hCd
    have hFt := Fbar_pos hf (hθb0.trans hopt.1.2.1)
    have hI := int_xf_nonneg hf le_rfl hθb0
    have hpos2 : 0 < (Cfun f αb K θb - Cfun f αb K 0) * Fbar f θt :=
      mul_pos (by nlinarith) hFt
    simp only [intervalIntegral.integral_same, sub_zero, zero_mul, add_zero] at hd
    nlinarith [mul_nonneg hαb0 hI]
  refine ⟨hb0, ?_⟩
  rw [hb0]; simp [dt, Fhatb_zero]

/-- `θ F̄(θ) > M* F(θ)` on `(0, g⁻¹(1)]`. -/
lemma G_pos (hf : DemandModel f) {θ : ℝ} (hθ : 0 < θ) (hθm : θ ≤ gInv1 f) :
    Mstar f * F f θ < θ * Fbar f θ := by
  have hm := m_pos hf
  have h1 : F f θ ≤ failureRate f θ * ∫ x in (0)..θ, Fbar f x := by
    have := intervalIntegral.integral_mono_on hθ.le (f_ii hf 0 θ)
      (((Fbar_cont hf).intervalIntegrable 0 θ).const_mul (failureRate f θ))
      (fun x hx => by
        rw [f_eq hf hx.1]
        exact mul_le_mul_of_nonneg_right (h_mono hf hx.1 hx.2) (Fbar_pos hf hx.1).le)
    rw [intervalIntegral.integral_const_mul] at this
    exact this
  have h2 : (∫ x in (0)..θ, Fbar f x) < θ := by
    have e : (∫ x in (0)..θ, Fbar f x) = θ - ∫ x in (0)..θ, F f x := by
      unfold Fbar
      rw [intervalIntegral.integral_sub intervalIntegrable_const ((F_cont hf).intervalIntegrable 0 θ)]
      simp
    have : 0 < ∫ x in (0)..θ, F f x := by
      apply intervalIntegral.intervalIntegral_pos_of_pos_on ((F_cont hf).intervalIntegrable 0 θ)
      · intro x hx
        have := F_strictMono hf le_rfl hx.1; rwa [F_zero] at this
      · exact hθ
    linarith
  have h3 : Mstar f * failureRate f θ ≤ Fbar f θ := by
    have hmh : failureRate f θ ≤ failureRate f (gInv1 f) := h_mono hf hθ.le hθm
    have hgm := g_m_le hf
    have e : Mstar f * failureRate f (gInv1 f) = Fbar f (gInv1 f) * genFailureRate f (gInv1 f) := by
      unfold Mstar genFailureRate; ring
    have hFm := Fbar_pos hf hm.le
    calc Mstar f * failureRate f θ ≤ Mstar f * failureRate f (gInv1 f) :=
          mul_le_mul_of_nonneg_left hmh (Mstar_pos hf).le
      _ = _ := e
      _ ≤ Fbar f (gInv1 f) * 1 := mul_le_mul_of_nonneg_left hgm hFm.le
      _ ≤ Fbar f θ := by rw [mul_one]; exact Fbar_anti hf hθm
  have hMh : 0 < Mstar f * failureRate f θ := mul_pos (Mstar_pos hf) (h_pos hf hθ.le)
  calc Mstar f * F f θ ≤ Mstar f * (failureRate f θ * ∫ x in (0)..θ, Fbar f x) :=
        mul_le_mul_of_nonneg_left h1 (Mstar_pos hf).le
    _ = (Mstar f * failureRate f θ) * ∫ x in (0)..θ, Fbar f x := by ring
    _ < (Mstar f * failureRate f θ) * θ := mul_lt_mul_of_pos_left h2 hMh
    _ ≤ Fbar f θ * θ := mul_le_mul_of_nonneg_right h3 hθ.le
    _ = θ * Fbar f θ := by ring

lemma G_unif (hf : DemandModel f) {η : ℝ} (hη : 0 < η) :
    ∃ γ > 0, ∀ θ, η ≤ θ → θ ≤ gInv1 f → γ ≤ θ * Fbar f θ - Mstar f * F f θ := by
  by_cases hηm : η ≤ gInv1 f
  · have hcont : ContinuousOn (fun θ => θ * Fbar f θ - Mstar f * F f θ) (Icc η (gInv1 f)) :=
      ((continuous_id.mul (Fbar_cont hf)).sub (continuous_const.mul (F_cont hf))).continuousOn
    obtain ⟨θ0, hθ0, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨η, le_rfl, hηm⟩ hcont
    refine ⟨θ0 * Fbar f θ0 - Mstar f * F f θ0, ?_, fun θ h1 h2 => hmin ⟨h1, h2⟩⟩
    have := G_pos hf (hη.trans_le hθ0.1) hθ0.2
    linarith
  · exact ⟨1, one_pos, fun θ h1 h2 => absurd (h1.trans h2) hηm⟩

/-- Part 3 of Proposition 3. -/
theorem part_net_highcash (hf : DemandModel f) {c αb αt : ℝ} (hc0 : 0 < c) (hαb0 : 0 ≤ αb)
    (hαt0 : 0 ≤ αt) (hαt1 : αt ≤ 1) :
    ∃ Klow : ℝ, Klow < Mstar f ∧ ∀ K : ℝ, 0 < K → Klow ≤ K → K < Mstar f →
      ∀ θb θt : ℝ, IsOptimalContract f c αb αt K θb θt → θb = 0 ∧ dt f αb θb = 0 := by
  have hM := Mstar_pos hf
  have hf0 := hf.pos 0 le_rfl
  obtain ⟨δ, hδ, hnear⟩ := f_near hf 0 le_rfl
  obtain ⟨η, hη, hηδ, hη4, hηc⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ δ ∧ η ≤ 1 / (4 * f 0) ∧ η ≤ c * Mstar f / 16 :=
    ⟨min (min δ (1 / (4 * f 0))) (c * Mstar f / 16), lt_min (lt_min hδ (by positivity)) (by positivity),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      min_le_right _ _⟩
  obtain ⟨γ, hγ, hG⟩ := G_unif hf hη
  refine ⟨max (Mstar f / 2) (Mstar f - γ / 2), max_lt (by linarith) (by linarith), ?_⟩
  intro K hK hKlow hKM θb θt hopt
  have hK1 : Mstar f / 2 ≤ K := (le_max_left _ _).trans hKlow
  have hK2 : Mstar f - γ / 2 ≤ K := (le_max_right _ _).trans hKlow
  have hmem := hopt.1
  obtain ⟨hFb, hC, hV, htm⟩ := mem_Theta_facts hf hc0 hαb0 hK hmem
  obtain ⟨g0, g1, g2, g3, g4⟩ := hmem
  simp only at g0 g1 g2 g3 g4
  have hFt := Fbar_pos hf (g0.trans g1)
  -- θt is small
  have htη : θt < η := by
    by_contra hge
    push Not at hge
    have hGt := hG θt hge htm
    have hFn := F_nonneg hf (g0.trans g1)
    have : (θt + K) * Fbar f θt ≤ (θt + Cfun f αb K θb) * Fbar f θt :=
      mul_le_mul_of_nonneg_right (by linarith) hFt.le
    have e : (θt + K) * Fbar f θt = θt * Fbar f θt + K - K * F f θt := by unfold Fbar; ring
    nlinarith [mul_le_mul_of_nonneg_right hKM.le hFn]
  have hb0 : θb = 0 := by
    by_contra hne
    have hpos : 0 < θb := lt_of_le_of_ne g0 (Ne.symm hne)
    obtain ⟨hmem0, hgap⟩ := shift hf hc0 hαb0 hK hopt.1 le_rfl g0
    have hle := opt_le hopt hmem0
    have hd := PiS_diff (f := f) c αb αt K θb θt 0
    have hCg := C_ge hf hαb0 hK g0 hFb
    rw [Cfun_zero] at hgap
    have hFhF := Fhatb_le_Fbar hf hαb0 g0
    -- gain ≥ c K F(θb) F̄(θt)
    have hgain : c * (K * F f θb * Fbar f θt) ≤ c * (Qfun f αb K θb θt - Qfun f αb K 0 θt) := by
      apply mul_le_mul_of_nonneg_left _ hc0.le
      have : K * F f θb ≤ Cfun f αb K θb - K := by unfold Fbar at hFhF; nlinarith
      nlinarith [mul_le_mul_of_nonneg_right this hFt.le]
    -- the αb term is ≥ 0
    have hI := int_xf_nonneg hf le_rfl g0
    -- the αt term
    have hsplit1 := intervalIntegral.integral_add_adjacent_intervals (xf_ii hf 0 θb 0) (xf_ii hf θb θt 0)
    have hA : ∫ x in θb..θt, (x - θb) * f x = (∫ x in θb..θt, x * f x) - θb * ∫ x in θb..θt, f x := by
      have : (fun x => (x - θb) * f x) = fun x => x * f x - θb * f x := by ext x; ring
      rw [this, intervalIntegral.integral_sub (xf_ii' hf θb θt) ((f_ii hf θb θt).const_mul θb),
        intervalIntegral.integral_const_mul]
    have hB : ∫ x in (0)..θb, x * f x ≤ θb * F f θb := by
      have := intervalIntegral.integral_mono_on g0 (xf_ii' hf 0 θb) ((f_ii hf 0 θb).const_mul θb)
        (fun x hx => mul_le_mul_of_nonneg_right hx.2 (f_nonneg hf x))
      rw [intervalIntegral.integral_const_mul] at this
      unfold F; exact this
    have hFsub := F_sub hf θb θt
    have hxf : ∀ r, (fun x => (x - r) * f x) = fun x => (x - r) * f x := fun _ => rfl
    simp only [sub_zero] at hsplit1
    have hαtterm : -(θb * F f θt) ≤
        (∫ x in θb..θt, (x - θb) * f x) - ∫ x in (0)..θt, (x - 0) * f x := by
      simp only [sub_zero]
      rw [← hsplit1, hA, ← hFsub]
      nlinarith
    have hαtterm' : -(θb * F f θt) ≤ αt * ((∫ x in θb..θt, (x - θb) * f x) - ∫ x in (0)..θt, (x - 0) * f x) := by
      have h0 : 0 ≤ θb * F f θt := mul_nonneg g0 (F_nonneg hf (g0.trans g1))
      have m1 := mul_le_mul_of_nonneg_left hαtterm hαt0
      have m2 := mul_nonneg (sub_nonneg.mpr hαt1) h0
      have e : αt * -(θb * F f θt) = -(αt * (θb * F f θt)) := by ring
      have e2 : (1 - αt) * (θb * F f θt) = θb * F f θt - αt * (θb * F f θt) := by ring
      linarith
    -- smallness bounds
    have hθtδ : θt ≤ δ := le_trans htη.le hηδ
    have hθt4 : θt ≤ 1 / (4 * f 0) := le_trans htη.le hη4
    have hθtc : θt < c * Mstar f / 16 := lt_of_lt_of_le htη hηc
    have hFb_lo : f 0 / 2 * (θb - 0) ≤ F f θb - F f 0 :=
      F_diff_ge hf g0 (fun x hx => (hnear x hx.1 (by rw [sub_zero, abs_of_nonneg hx.1]; linarith [hx.2])).1)
    have hFt_hi : F f θt - F f 0 ≤ 2 * f 0 * (θt - 0) :=
      F_diff_le hf (g0.trans g1) (fun x hx => (hnear x hx.1 (by rw [sub_zero, abs_of_nonneg hx.1]; linarith [hx.2])).2)
    rw [F_zero, sub_zero, sub_zero] at hFb_lo hFt_hi
    have hθt4' : θt * (4 * f 0) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at hθt4
    have hFbar_lo : 1 / 2 ≤ Fbar f θt := by unfold Fbar; linarith
    -- c K F(θb) F̄(θt) > θb F(θt)
    have key : θb * F f θt < c * (K * F f θb * Fbar f θt) := by
      have e1 : θb * F f θt ≤ θb * (2 * f 0 * θt) := mul_le_mul_of_nonneg_left hFt_hi g0
      have e2 : c * (K * (f 0 / 2 * θb) * (1 / 2)) ≤ c * (K * F f θb * Fbar f θt) := by
        apply mul_le_mul_of_nonneg_left _ hc0.le
        apply mul_le_mul (mul_le_mul_of_nonneg_left hFb_lo hK.le) hFbar_lo (by norm_num)
          (mul_nonneg hK.le (F_nonneg hf g0))
      have e3 : θb * (2 * f 0 * θt) < c * (K * (f 0 / 2 * θb) * (1 / 2)) := by
        have hcK := mul_le_mul_of_nonneg_left hK1 hc0.le
        have : 2 * θt < c * K / 4 := by linarith
        have hp : 0 < θb * f 0 := mul_pos hpos hf0
        have m := mul_lt_mul_of_pos_left this hp
        have q1 : θb * (2 * f 0 * θt) = θb * f 0 * (2 * θt) := by ring
        have q2 : c * (K * (f 0 / 2 * θb) * (1 / 2)) = θb * f 0 * (c * K / 4) := by ring
        rw [q1, q2]; exact m
      linarith
    simp only [intervalIntegral.integral_same, sub_zero] at hd hαtterm'
    have := mul_nonneg hαb0 hI
    linarith
  refine ⟨hb0, ?_⟩
  rw [hb0]; simp [dt, Fhatb_zero]

/-- Part 1 of Proposition 3. -/
theorem part_tc_used (hf : DemandModel f) {c αb αt : ℝ} (hc0 : 0 < c) (hαb0 : 0 ≤ αb)
    (hαt0 : 0 ≤ αt) (hαt1 : αt ≤ 1) {K : ℝ} (hK : 0 < K) {θb θt : ℝ}
    (hopt : IsOptimalContract f c αb αt K θb θt) (ht : 0 < θt) : θb < θt := by
  have hmem := hopt.1
  obtain ⟨g0, g1, g2, g3, g4⟩ := hmem
  simp only at g0 g1 g2 g3 g4
  rcases g1.lt_or_eq with hlt | heq
  · exact hlt
  exfalso
  subst heq
  set θ := θb with hθdef
  have hF := mem_Theta_Fhatb_pos hf hc0 hopt.1
  have hw := w_pos_of hf g0 hF
  have hFt := Fbar_pos hf g0
  have hfθ := hf.pos θ g0
  obtain ⟨δ, hδ, hnear⟩ := f_near hf θ g0
  obtain ⟨A, hA, hApos⟩ : ∃ A : ℝ, A = c * K * (1 - αb * genFailureRate f θ) * Fbar f θ * (f θ / 2) ∧ 0 < A :=
    ⟨_, rfl, by positivity⟩
  obtain ⟨ε, hε, hεδ, hεθ, hεA⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ δ ∧ ε ≤ θ ∧ ε ≤ A / (4 * f θ) :=
    ⟨min (min δ θ) (A / (4 * f θ)), lt_min (lt_min hδ ht) (by positivity),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      min_le_right _ _⟩
  have hεA' : ε * (4 * f θ) ≤ A := by rwa [le_div_iff₀ (by positivity)] at hεA
  obtain ⟨θ', hθ'⟩ : ∃ θ' : ℝ, θ' = θ - ε := ⟨_, rfl⟩
  have h0' : 0 ≤ θ' := by linarith
  have h1' : θ' ≤ θ := by linarith
  obtain ⟨hmem', hgap⟩ := shift hf hc0 hαb0 hK hopt.1 h0' h1'
  have hle := opt_le hopt hmem'
  have hd := PiS_diff (f := f) c αb αt K θ θ θ'
  have hCd := C_diff hf hαb0 hK h0' h1' hF
  -- F̂(θ') - F̂(θ) ≥ (F θ - F θ') w(θ)
  have hgle : genFailureRate f θ' ≤ genFailureRate f θ := g_mono hf h0' h1'
  have hFh : (F f θ - F f θ') * (1 - αb * genFailureRate f θ) ≤ Fhatb f αb θ' - Fhatb f αb θ := by
    unfold Fhatb Fbar
    have hF'pos := Fbar_pos hf h0'
    unfold Fbar at hF'pos
    nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgle hαb0) hF'pos.le]
  have hFlo : f θ / 2 * (θ - θ') ≤ F f θ - F f θ' :=
    F_diff_ge hf h1' (fun x hx => (hnear x (h0'.trans hx.1)
      (by rw [abs_of_nonpos (by linarith [hx.2])]; linarith [hx.1])).1)
  have hgain : A * ε ≤ c * (Qfun f αb K θ θ - Qfun f αb K θ' θ) := by
    have e1 : (f θ / 2 * ε) * (1 - αb * genFailureRate f θ) ≤ Fhatb f αb θ' - Fhatb f αb θ := by
      have : θ - θ' = ε := by rw [hθ']; ring
      rw [this] at hFlo
      linarith [mul_le_mul_of_nonneg_right hFlo hw.le]
    have e2 : K * ((f θ / 2 * ε) * (1 - αb * genFailureRate f θ)) * Fbar f θ ≤
        (Cfun f αb K θ - Cfun f αb K θ') * Fbar f θ :=
      mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left e1 hK.le).trans hCd) hFt.le
    have e3 := mul_le_mul_of_nonneg_left (e2.trans hgap) hc0.le
    have : A * ε = c * (K * ((f θ / 2 * ε) * (1 - αb * genFailureRate f θ)) * Fbar f θ) := by
      rw [hA]; ring
    linarith
  have hαbterm : 0 ≤ (∫ x in (0)..θ, x * f x) - ∫ x in (0)..θ', x * f x := by
    have := intervalIntegral.integral_add_adjacent_intervals (xf_ii' hf 0 θ') (xf_ii' hf θ' θ)
    have := int_xf_nonneg hf h0' h1'
    linarith
  have hαtterm : ∫ x in θ'..θ, (x - θ') * f x ≤ 2 * f θ * ε * ε := by
    have := intervalIntegral.integral_mono_on h1' (xf_ii hf θ' θ θ') intervalIntegrable_const
      (fun x hx => show (x - θ') * f x ≤ 2 * f θ * ε by
        have hb := (hnear x (h0'.trans hx.1)
          (by rw [abs_of_nonpos (by linarith [hx.2])]; linarith [hx.1])).2
        have hx1 : x - θ' ≤ ε := by linarith [hx.2]
        have hx0 : 0 ≤ x - θ' := by linarith [hx.1]
        nlinarith [f_nonneg hf x])
    simp only [intervalIntegral.integral_const, smul_eq_mul] at this
    have e : θ - θ' = ε := by rw [hθ']; ring
    rw [e] at this; linarith
  have hnn : 0 ≤ ∫ x in θ'..θ, (x - θ') * f x :=
    intervalIntegral.integral_nonneg h1' (fun x hx => mul_nonneg (by linarith [hx.1]) (f_nonneg hf x))
  simp only [intervalIntegral.integral_same, zero_sub] at hd
  have hαt' : αt * (∫ x in θ'..θ, (x - θ') * f x) ≤ 2 * f θ * ε * ε := by
    have := mul_le_mul_of_nonneg_right hαt1 hnn
    linarith
  have h4 := mul_le_mul_of_nonneg_right hεA' hε.le
  have h5 : 0 < f θ * ε * ε := by positivity
  have e1 : ε * (4 * f θ) * ε = 4 * (f θ * ε * ε) := by ring
  have e2 : 2 * f θ * ε * ε = 2 * (f θ * ε * ε) := by ring
  have e3 : αt * -(∫ x in θ'..θ, (x - θ') * f x) = -(αt * (∫ x in θ'..θ, (x - θ') * f x)) := by ring
  rw [e3] at hd
  have := mul_nonneg hαb0 hαbterm
  linarith

end Aux
end TradeCredit.Terms

open TradeCredit.Terms TradeCredit.Terms.Aux in
theorem solution (f : ℝ → ℝ) (hf : DemandModel f)
    (c αb αt : ℝ) (hc0 : 0 < c) (hc1 : c < 1) (hαb0 : 0 ≤ αb) (hαb1 : αb ≤ 1)
    (hαt0 : 0 ≤ αt) (hαt1 : αt ≤ 1) :
    -- trade credit is always used when external financing is used
    (∀ K : ℝ, 0 < K → ∀ θb θt : ℝ, IsOptimalContract f c αb αt K θb θt →
        0 < θt → θb < θt) ∧
    -- 1. α_t = 0: net terms, no bank loan
    (αt = 0 → ∀ K : ℝ, 0 < K → ∀ θb θt : ℝ, IsOptimalContract f c αb αt K θb θt →
        θb = 0 ∧ dt f αb θb = 0) ∧
    -- 1. K sufficiently large (below M*): net terms, no bank loan
    (∃ Klow : ℝ, Klow < Mstar f ∧ ∀ K : ℝ, 0 < K → Klow ≤ K → K < Mstar f →
        ∀ θb θt : ℝ, IsOptimalContract f c αb αt K θb θt → θb = 0 ∧ dt f αb θb = 0) ∧
    -- 2. α_t > 0 and K sufficiently small: two-part terms, bank loan and trade credit
    (0 < αt → ∃ Khigh : ℝ, 0 < Khigh ∧ ∀ K : ℝ, 0 < K → K < Khigh →
        ∀ θb θt : ℝ, IsOptimalContract f c αb αt K θb θt →
          0 < θb ∧ θb < θt ∧ 0 < dt f αb θb) := by
  refine ⟨fun K hK θb θt hopt ht => part_tc_used hf hc0 hαb0 hαt0 hαt1 hK hopt ht,
    fun hαt K hK θb θt hopt => part_net_alpha0 hf hc0 hαb0 hαt hK hopt,
    part_net_highcash hf hc0 hαb0 hαt0 hαt1, fun hαt => ?_⟩
  obtain ⟨Kh, hKh, hlow⟩ := proposition3_two_part_low_cash f hf c αb αt hc0 hc1 hαb0 hαb1 hαt hαt1
  refine ⟨Kh, hKh, fun K hK hKK θb θt hopt => ?_⟩
  have hb := hlow K hK hKK θb θt hopt
  have hbt : θb < θt := part_tc_used hf hc0 hαb0 hαt0 hαt1 hK hopt
    (lt_of_lt_of_le hb hopt.1.2.1)
  have hF := mem_Theta_Fhatb_pos hf hc0 hopt.1
  have hs := Fhatb_strictAnti hf hαb0 hF le_rfl hb le_rfl
  rw [Fhatb_zero] at hs
  refine ⟨hb, hbt, ?_⟩
  unfold dt; linarith
