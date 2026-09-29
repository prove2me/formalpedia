-- Prove2me | solution 1 for ZhengQR.CostBounds.cost_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:36:30.661406+00:00
-- url     : https://prove2.me/submissions/909b3ac1-18d8-46d9-9d27-de9ed5c52a06

import Mathlib
import Definitions.Def_ZhengQR_CostBounds_QRMachinery
import Definitions.Def_ZhengQR_CostBounds_Model

namespace ZhengQR.CostBounds

open MeasureTheory Filter Topology

/-- Abstract properties of the inventory-cost rate used in the proof. -/
structure aux_cd_Good (G : ℝ → ℝ) : Prop where
  lip : ∃ L : ℝ, 0 < L ∧ ∀ y y' : ℝ, |G y - G y'| ≤ L * |y - y'|
  conv : ∀ x z a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → G (a * x + b * z) ≤ a * G x + b * G z
  coer : ∃ c1 c2 m : ℝ, 0 < c1 ∧ 0 < c2 ∧ ∀ y : ℝ, c1 * (y - m) ≤ G y ∧ c2 * (m - y) ≤ G y
  umin : ∃! y : ℝ, ∀ z : ℝ, G y ≤ G z

section NV

variable {μ : Measure ℝ} [IsProbabilityMeasure μ] {h p : ℝ}

lemma aux_cd_int (hid : Integrable (fun x : ℝ => x) μ) (y : ℝ) :
    Integrable (fun x => h * max (y - x) 0 + p * max (x - y) 0) μ :=
  (((integrable_const y).sub hid).pos_part.const_mul h).add
    ((hid.sub (integrable_const y)).pos_part.const_mul p)

lemma aux_cd_lip (hid : Integrable (fun x : ℝ => x) μ) (hh : 0 < h) (hp : 0 < p) (y y' : ℝ) :
    |newsvendorCost μ h p y - newsvendorCost μ h p y'| ≤ (h + p) * |y - y'| := by
  unfold newsvendorCost
  rw [← integral_sub (aux_cd_int hid y) (aux_cd_int hid y')]
  have := norm_integral_le_of_norm_le_const (μ := μ) (C := (h + p) * |y - y'|)
    (f := fun x => h * max (y - x) 0 + p * max (x - y) 0 -
      (h * max (y' - x) 0 + p * max (x - y') 0))
    (ae_of_all _ fun x => by
      have h1 := abs_max_sub_max_le_abs (y - x) (y' - x) 0
      have h2 := abs_max_sub_max_le_abs (x - y) (x - y') 0
      rw [show (y - x) - (y' - x) = y - y' by ring] at h1
      rw [show (x - y) - (x - y') = -(y - y') by ring, abs_neg] at h2
      rw [Real.norm_eq_abs]
      calc |h * max (y - x) 0 + p * max (x - y) 0 - (h * max (y' - x) 0 + p * max (x - y') 0)|
          = |h * (max (y - x) 0 - max (y' - x) 0) + p * (max (x - y) 0 - max (x - y') 0)| := by
            congr 1; ring
        _ ≤ |h * (max (y - x) 0 - max (y' - x) 0)| + |p * (max (x - y) 0 - max (x - y') 0)| :=
            abs_add_le _ _
        _ = h * |max (y - x) 0 - max (y' - x) 0| + p * |max (x - y) 0 - max (x - y') 0| := by
            rw [abs_mul, abs_mul, abs_of_pos hh, abs_of_pos hp]
        _ ≤ h * |y - y'| + p * |y - y'| := by gcongr
        _ = (h + p) * |y - y'| := by ring)
  simpa using this

lemma aux_cd_conv (hid : Integrable (fun x : ℝ => x) μ) (hh : 0 < h) (hp : 0 < p)
    (x z a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    newsvendorCost μ h p (a * x + b * z) ≤
      a * newsvendorCost μ h p x + b * newsvendorCost μ h p z := by
  unfold newsvendorCost
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((aux_cd_int hid x).const_mul a) ((aux_cd_int hid z).const_mul b)]
  apply integral_mono (aux_cd_int hid _)
    (((aux_cd_int hid x).const_mul a).add ((aux_cd_int hid z).const_mul b))
  intro w
  have hw : a * w + b * w = w := by rw [← add_mul, hab, one_mul]
  have e1 : max (a * x + b * z - w) 0 ≤ a * max (x - w) 0 + b * max (z - w) 0 := by
    apply max_le
    · have i1 := mul_le_mul_of_nonneg_left (le_max_left (x - w) 0) ha
      have i2 := mul_le_mul_of_nonneg_left (le_max_left (z - w) 0) hb
      linarith
    · exact add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))
  have e2 : max (w - (a * x + b * z)) 0 ≤ a * max (w - x) 0 + b * max (w - z) 0 := by
    apply max_le
    · have i1 := mul_le_mul_of_nonneg_left (le_max_left (w - x) 0) ha
      have i2 := mul_le_mul_of_nonneg_left (le_max_left (w - z) 0) hb
      linarith
    · exact add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))
  simp only [Pi.add_apply]
  linarith [mul_le_mul_of_nonneg_left e1 hh.le, mul_le_mul_of_nonneg_left e2 hp.le]

lemma aux_cd_coer (hid : Integrable (fun x : ℝ => x) μ) (hh : 0 < h) (hp : 0 < p) (y : ℝ) :
    h * (y - ∫ x, x ∂μ) ≤ newsvendorCost μ h p y ∧
      p * ((∫ x, x ∂μ) - y) ≤ newsvendorCost μ h p y := by
  constructor
  · have e : h * (y - ∫ x, x ∂μ) = ∫ x, h * (y - x) ∂μ := by
      rw [integral_const_mul, integral_sub (integrable_const y) hid, integral_const]; simp
    rw [e]; unfold newsvendorCost
    apply integral_mono (((integrable_const y).sub hid).const_mul h) (aux_cd_int hid y)
    intro x
    simp only [Pi.sub_apply]
    linarith [mul_le_mul_of_nonneg_left (le_max_left (y - x) 0) hh.le,
      mul_nonneg hp.le (le_max_right (x - y) 0)]
  · have e : p * ((∫ x, x ∂μ) - y) = ∫ x, p * (x - y) ∂μ := by
      rw [integral_const_mul, integral_sub hid (integrable_const y), integral_const]; simp
    rw [e]; unfold newsvendorCost
    apply integral_mono ((hid.sub (integrable_const y)).const_mul p) (aux_cd_int hid y)
    intro x
    simp only [Pi.sub_apply]
    linarith [mul_le_mul_of_nonneg_left (le_max_left (x - y) 0) hp.le,
      mul_nonneg hh.le (le_max_right (y - x) 0)]

end NV

section Abstract

variable {G : ℝ → ℝ}

/-- Antiderivative of `G`. -/
noncomputable def aux_cd_Phi (G : ℝ → ℝ) (u : ℝ) : ℝ := ∫ y in (0 : ℝ)..u, G y

/-- The chosen reorder point, extended by `y⁰` for `t ≤ 0`. -/
noncomputable def aux_cd_rho (G : ℝ → ℝ) (lam K t : ℝ) : ℝ :=
  if 0 < t then reorderPt G lam K t else idealPt G

/-- `F(t) = ∫_{r(t)}^{r(t)+t} G`. -/
noncomputable def aux_cd_F (G : ℝ → ℝ) (lam K t : ℝ) : ℝ :=
  aux_cd_Phi G (aux_cd_rho G lam K t + t) - aux_cd_Phi G (aux_cd_rho G lam K t)

lemma aux_cd_cont (hG : aux_cd_Good G) : Continuous G := by
  obtain ⟨L, hL, hlip⟩ := hG.lip
  have : LipschitzWith ⟨L, hL.le⟩ G := LipschitzWith.of_dist_le_mul fun x y => by
    rw [Real.dist_eq, Real.dist_eq]; exact hlip x y
  exact this.continuous

lemma aux_cd_Phi_deriv (hG : aux_cd_Good G) (u : ℝ) : HasDerivAt (aux_cd_Phi G) (G u) u :=
  ((aux_cd_cont hG).integral_hasStrictDerivAt 0 u).hasDerivAt

lemma aux_cd_Phi_cont (hG : aux_cd_Good G) : Continuous (aux_cd_Phi G) :=
  continuous_iff_continuousAt.2 fun u => (aux_cd_Phi_deriv hG u).continuousAt

lemma aux_cd_int_eq (hG : aux_cd_Good G) (a b : ℝ) :
    ∫ y in a..b, G y = aux_cd_Phi G b - aux_cd_Phi G a := by
  unfold aux_cd_Phi
  rw [intervalIntegral.integral_interval_sub_left ((aux_cd_cont hG).intervalIntegrable _ _)
    ((aux_cd_cont hG).intervalIntegrable _ _)]

lemma aux_cd_ideal (hG : aux_cd_Good G) :
    (∀ z, G (idealPt G) ≤ G z) ∧ ∀ y, (∀ z, G y ≤ G z) → y = idealPt G := by
  have hex : ∃ y, ∀ z, G y ≤ G z := hG.umin.exists
  have hmin : ∀ z, G (idealPt G) ≤ G z := by
    unfold idealPt; rw [dif_pos hex]; exact hex.choose_spec
  exact ⟨hmin, fun y hy => hG.umin.unique hy hmin⟩

lemma aux_cd_strict (hG : aux_cd_Good G) {x : ℝ} (hx : x ≠ idealPt G) :
    G (idealPt G) < G x := by
  obtain ⟨hmin, huniq⟩ := aux_cd_ideal hG
  rcases (hmin x).lt_or_eq with h | h
  · exact h
  · exfalso; apply hx; apply huniq; intro z; rw [← h]; exact hmin z

lemma aux_cd_chord (hG : aux_cd_Good G) {x y z : ℝ} (hxy : x < y) (hyz : y < z) :
    (z - x) * G y ≤ (z - y) * G x + (y - x) * G z := by
  have hd : 0 < z - x := by linarith
  have hne : z - x ≠ 0 := hd.ne'
  have h := hG.conv x z ((z - y) / (z - x)) ((y - x) / (z - x)) (div_nonneg (by linarith) hd.le)
    (div_nonneg (by linarith) hd.le) (by field_simp; ring)
  have e : (z - y) / (z - x) * x + (y - x) / (z - x) * z = y := by field_simp; ring
  rw [e] at h
  have h2 := mul_le_mul_of_nonneg_left h hd.le
  have e2 : (z - x) * ((z - y) / (z - x) * G x + (y - x) / (z - x) * G z) =
      (z - y) * G x + (y - x) * G z := by field_simp
  linarith

lemma aux_cd_left (hG : aux_cd_Good G) {x x' : ℝ} (hxx : x < x') (hx' : x' ≤ idealPt G) :
    G x' < G x := by
  have hs : G (idealPt G) < G x := aux_cd_strict hG (ne_of_lt (lt_of_lt_of_le hxx hx'))
  rcases hx'.lt_or_eq with h | h
  · have h1 := aux_cd_chord hG hxx h
    have h2 := mul_lt_mul_of_pos_left hs (sub_pos.2 hxx)
    have h3 : (idealPt G - x) * G x' < (idealPt G - x) * G x := by linarith
    exact lt_of_mul_lt_mul_left h3 (by linarith)
  · rw [h]; exact hs

lemma aux_cd_right (hG : aux_cd_Good G) {x x' : ℝ} (hx : idealPt G ≤ x) (hxx : x < x') :
    G x < G x' := by
  have hs : G (idealPt G) < G x' := aux_cd_strict hG (ne_of_gt (lt_of_le_of_lt hx hxx))
  rcases hx.lt_or_eq with h | h
  · have h1 := aux_cd_chord hG h hxx
    have h2 := mul_lt_mul_of_pos_left hs (sub_pos.2 hxx)
    have h3 : (x' - idealPt G) * G x < (x' - idealPt G) * G x' := by linarith
    exact lt_of_mul_lt_mul_left h3 (by linarith)
  · rw [← h]; exact hs

lemma aux_cd_opt_iff {lam K t r : ℝ} (ht : 0 < t) :
    IsOptReorder G lam K t r ↔ ∀ r', ∫ y in r..r + t, G y ≤ ∫ y in r'..r' + t, G y := by
  unfold IsOptReorder qrCost
  constructor
  · intro H r'; have := H r'; rw [div_le_div_iff_of_pos_right ht] at this; linarith
  · intro H r'; rw [div_le_div_iff_of_pos_right ht]; linarith [H r']

lemma aux_cd_exists (hG : aux_cd_Good G) (lam K : ℝ) {t : ℝ} (ht : 0 < t) :
    ∃ r, IsOptReorder G lam K t r := by
  obtain ⟨c1, c2, m, hc1, hc2, hco⟩ := hG.coer
  set ψ : ℝ → ℝ := fun r => ∫ y in r..r + t, G y with hψ
  have hψc : Continuous ψ := by
    have : ψ = fun r => aux_cd_Phi G (r + t) - aux_cd_Phi G r := by
      funext r; exact aux_cd_int_eq hG _ _
    rw [this]
    exact ((aux_cd_Phi_cont hG).comp (continuous_add_const t)).sub (aux_cd_Phi_cont hG)
  have lb1 : ∀ r, t * (c1 * (r - m)) ≤ ψ r := by
    intro r
    have := intervalIntegral.integral_mono_on (show r ≤ r + t by linarith)
      (intervalIntegrable_const : IntervalIntegrable (fun _ => c1 * (r - m)) volume r (r + t)) ((aux_cd_cont hG).intervalIntegrable _ _)
      (fun y hy => le_trans (mul_le_mul_of_nonneg_left (by linarith [hy.1]) hc1.le) (hco y).1)
    rw [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] at this
    exact this
  have lb2 : ∀ r, t * (c2 * (m - (r + t))) ≤ ψ r := by
    intro r
    have := intervalIntegral.integral_mono_on (show r ≤ r + t by linarith)
      (intervalIntegrable_const :
        IntervalIntegrable (fun _ => c2 * (m - (r + t))) volume r (r + t))
      ((aux_cd_cont hG).intervalIntegrable _ _)
      (fun y hy => le_trans (mul_le_mul_of_nonneg_left (by linarith [hy.2]) hc2.le) (hco y).2)
    rw [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] at this
    exact this
  have hlim : Tendsto ψ (cocompact ℝ) atTop := by
    rw [cocompact_eq_atBot_atTop, tendsto_sup]
    constructor
    · rw [tendsto_atBot_atTop]
      intro b
      refine ⟨m - t - |b| / (t * c2), fun r hr => ?_⟩
      have h1 := lb2 r
      have htc : 0 < t * c2 := mul_pos ht hc2
      have h2 : |b| / (t * c2) ≤ m - (r + t) := by linarith
      rw [div_le_iff₀ htc] at h2
      linarith [le_abs_self b]
    · rw [tendsto_atTop_atTop]
      intro b
      refine ⟨m + |b| / (t * c1), fun r hr => ?_⟩
      have h1 := lb1 r
      have htc : 0 < t * c1 := mul_pos ht hc1
      have h2 : |b| / (t * c1) ≤ r - m := by linarith
      rw [div_le_iff₀ htc] at h2
      linarith [le_abs_self b]
  obtain ⟨r, hr⟩ := hψc.exists_forall_le hlim
  exact ⟨r, (aux_cd_opt_iff ht).2 hr⟩

lemma aux_cd_rho_opt (hG : aux_cd_Good G) (lam K : ℝ) {t : ℝ} (ht : 0 < t) :
    IsOptReorder G lam K t (aux_cd_rho G lam K t) := by
  have hex := aux_cd_exists hG lam K ht
  unfold aux_cd_rho reorderPt
  rw [if_pos ht, dif_pos hex]
  exact hex.choose_spec

lemma aux_cd_foc (hG : aux_cd_Good G) {lam K t r : ℝ} (ht : 0 < t)
    (hr : IsOptReorder G lam K t r) : G r = G (r + t) := by
  have hmin := (aux_cd_opt_iff ht).1 hr
  have hd : HasDerivAt (fun u => aux_cd_Phi G (u + t) - aux_cd_Phi G u) (G (r + t) - G r) r :=
    ((aux_cd_Phi_deriv hG (r + t)).comp_add_const r t).sub (aux_cd_Phi_deriv hG r)
  have hloc : IsLocalMin (fun u => aux_cd_Phi G (u + t) - aux_cd_Phi G u) r :=
    Filter.Eventually.of_forall fun u => by
      simp only
      rw [← aux_cd_int_eq hG, ← aux_cd_int_eq hG]; exact hmin u
  have := hloc.hasDerivAt_eq_zero hd
  linarith

lemma aux_cd_pos (hG : aux_cd_Good G) {lam K t r : ℝ} (ht : 0 < t)
    (hr : IsOptReorder G lam K t r) : r < idealPt G ∧ idealPt G < r + t := by
  have hf := aux_cd_foc hG ht hr
  constructor
  · by_contra hc; push Not at hc
    have := aux_cd_right hG hc (show r < r + t by linarith); linarith
  · by_contra hc; push Not at hc
    have := aux_cd_left hG (show r < r + t by linarith) hc; linarith

lemma aux_cd_mono (hG : aux_cd_Good G) (lam K : ℝ) {s t : ℝ} (hs : 0 < s) (hst : s < t) :
    aux_cd_rho G lam K t ≤ aux_cd_rho G lam K s ∧
      aux_cd_rho G lam K s ≤ aux_cd_rho G lam K t + (t - s) := by
  have ht : 0 < t := by linarith
  have hoa := aux_cd_rho_opt hG lam K hs
  have hob := aux_cd_rho_opt hG lam K ht
  have fa := aux_cd_foc hG hs hoa
  have fb := aux_cd_foc hG ht hob
  obtain ⟨pa1, pa2⟩ := aux_cd_pos hG hs hoa
  obtain ⟨pb1, pb2⟩ := aux_cd_pos hG ht hob
  constructor
  · by_contra hc; push Not at hc
    have e1 := aux_cd_left hG hc pb1.le
    have e2 := aux_cd_right hG pa2.le
      (show aux_cd_rho G lam K s + s < aux_cd_rho G lam K t + t by linarith)
    linarith
  · by_contra hc; push Not at hc
    have e1 := aux_cd_right hG pb2.le
      (show aux_cd_rho G lam K t + t < aux_cd_rho G lam K s + s by linarith)
    have e2 := aux_cd_left hG (show aux_cd_rho G lam K t < aux_cd_rho G lam K s by linarith)
      pa1.le
    linarith

lemma aux_cd_rho_lip_le (hG : aux_cd_Good G) (lam K : ℝ) {s t : ℝ} (hst : s ≤ t) :
    |aux_cd_rho G lam K t - aux_cd_rho G lam K s| ≤ t - s := by
  rcases le_or_gt t 0 with ht | ht
  · have hs : ¬ 0 < s := by linarith
    have ht' : ¬ 0 < t := by linarith
    simp only [aux_cd_rho, if_neg hs, if_neg ht', sub_self, abs_zero]; linarith
  · rcases le_or_gt s 0 with hs | hs
    · have hs' : ¬ 0 < s := by linarith
      have e : aux_cd_rho G lam K s = idealPt G := by simp only [aux_cd_rho, if_neg hs']
      rw [e]
      obtain ⟨p1, p2⟩ := aux_cd_pos hG ht (aux_cd_rho_opt hG lam K ht)
      rw [abs_le]; constructor <;> linarith
    · rcases hst.lt_or_eq with h | h
      · obtain ⟨m1, m2⟩ := aux_cd_mono hG lam K hs h
        rw [abs_le]; constructor <;> linarith
      · subst h; simp

lemma aux_cd_rho_lip (hG : aux_cd_Good G) (lam K s t : ℝ) :
    |aux_cd_rho G lam K t - aux_cd_rho G lam K s| ≤ |t - s| := by
  rcases le_total s t with h | h
  · exact (aux_cd_rho_lip_le hG lam K h).trans (le_abs_self _)
  · rw [abs_sub_comm, abs_sub_comm t s]
    exact (aux_cd_rho_lip_le hG lam K h).trans (le_abs_self _)

lemma aux_cd_rho_cont (hG : aux_cd_Good G) (lam K : ℝ) : Continuous (aux_cd_rho G lam K) := by
  have : LipschitzWith 1 (aux_cd_rho G lam K) := LipschitzWith.of_dist_le_mul fun x y => by
    simpa [Real.dist_eq] using aux_cd_rho_lip hG lam K y x
  exact this.continuous

lemma aux_cd_H_eq (lam K t : ℝ) : Hfun G lam K t = G (aux_cd_rho G lam K t) := by
  unfold Hfun aux_cd_rho; split_ifs <;> rfl

lemma aux_cd_H_cont (hG : aux_cd_Good G) (lam K : ℝ) : Continuous (Hfun G lam K) := by
  have : Hfun G lam K = fun t => G (aux_cd_rho G lam K t) := funext (aux_cd_H_eq lam K)
  rw [this]; exact (aux_cd_cont hG).comp (aux_cd_rho_cont hG lam K)

lemma aux_cd_Phi_quad (hG : aux_cd_Good G) {L : ℝ} (hL : 0 < L)
    (hlip : ∀ y y', |G y - G y'| ≤ L * |y - y'|) (a d : ℝ) :
    |aux_cd_Phi G (a + d) - aux_cd_Phi G a - d * G a| ≤ L * d ^ 2 := by
  have hc := aux_cd_cont hG
  have e : aux_cd_Phi G (a + d) - aux_cd_Phi G a - d * G a = ∫ y in a..a + d, (G y - G a) := by
    rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_const, aux_cd_int_eq hG]
    simp
  rw [e]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := a + d)
    (C := L * |d|) (f := fun y => G y - G a) (fun x hx => by
      rw [Real.norm_eq_abs]
      refine (hlip x a).trans (mul_le_mul_of_nonneg_left ?_ hL.le)
      rw [Set.mem_uIoc] at hx
      rw [abs_le]
      rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
        constructor <;> linarith [le_abs_self d, neg_abs_le d, abs_nonneg d])
  rw [Real.norm_eq_abs] at hb
  calc _ ≤ L * |d| * |a + d - a| := hb
    _ = L * d ^ 2 := by rw [add_sub_cancel_left, mul_assoc, ← sq, sq_abs]

lemma aux_cd_F_quad (hG : aux_cd_Good G) {L : ℝ} (hL : 0 < L)
    (hlip : ∀ y y', |G y - G y'| ≤ L * |y - y'|) (lam K : ℝ) {t t' : ℝ} (ht : 0 < t)
    (ht' : 0 < t') :
    |aux_cd_F G lam K t' - aux_cd_F G lam K t - (t' - t) * Hfun G lam K t| ≤
      3 * L * (t' - t) ^ 2 := by
  have hH : Hfun G lam K t = G (aux_cd_rho G lam K t + t) := by
    rw [aux_cd_H_eq, aux_cd_foc hG ht (aux_cd_rho_opt hG lam K ht)]
  have ho := (aux_cd_opt_iff ht).1 (aux_cd_rho_opt hG lam K ht)
  have ho' := (aux_cd_opt_iff ht').1 (aux_cd_rho_opt hG lam K ht')
  have hl := aux_cd_rho_lip hG lam K t t'
  rw [hH]
  unfold aux_cd_F
  set r := aux_cd_rho G lam K t with hr
  set r' := aux_cd_rho G lam K t' with hr'
  simp only [aux_cd_int_eq hG] at ho ho'
  have u1 := ho' r
  have u2 := ho r'
  have q1 := aux_cd_Phi_quad hG hL hlip (r + t) (t' - t)
  have q2 := aux_cd_Phi_quad hG hL hlip (r' + t) (t' - t)
  rw [show r + t + (t' - t) = r + t' by ring] at q1
  rw [show r' + t + (t' - t) = r' + t' by ring] at q2
  have l1 : |G (r' + t) - G (r + t)| ≤ L * |t' - t| := (hlip _ _).trans (by
    rw [show r' + t - (r + t) = r' - r by ring]
    exact mul_le_mul_of_nonneg_left hl hL.le)
  have l2 : |(t' - t) * (G (r' + t) - G (r + t))| ≤ L * (t' - t) ^ 2 := by
    rw [abs_mul]
    calc |t' - t| * |G (r' + t) - G (r + t)| ≤ |t' - t| * (L * |t' - t|) :=
          mul_le_mul_of_nonneg_left l1 (abs_nonneg _)
      _ = L * (t' - t) ^ 2 := by rw [← sq_abs (t' - t)]; ring
  obtain ⟨q1a, q1b⟩ := abs_le.1 q1
  obtain ⟨q2a, q2b⟩ := abs_le.1 q2
  obtain ⟨l2a, l2b⟩ := abs_le.1 l2
  have hsq : 0 ≤ L * (t' - t) ^ 2 := mul_nonneg hL.le (sq_nonneg _)
  rw [abs_le]; constructor <;> nlinarith

lemma aux_cd_F_deriv (hG : aux_cd_Good G) (lam K : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (aux_cd_F G lam K) (Hfun G lam K t) t := by
  obtain ⟨L, hL, hlip⟩ := hG.lip
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have h3L : 0 < 3 * L := by linarith
  have hball : Metric.ball t (min t (c / (3 * L))) ∈ 𝓝 t :=
    Metric.ball_mem_nhds _ (lt_min ht (div_pos hc h3L))
  filter_upwards [hball] with t' ht'
  rw [Metric.mem_ball, Real.dist_eq] at ht'
  have h1 : |t' - t| < t := lt_of_lt_of_le ht' (min_le_left _ _)
  have h2 : |t' - t| < c / (3 * L) := lt_of_lt_of_le ht' (min_le_right _ _)
  have ht'pos : 0 < t' := by have := neg_abs_le (t' - t); linarith
  have hq := aux_cd_F_quad hG hL hlip lam K ht ht'pos
  rw [Real.norm_eq_abs, Real.norm_eq_abs, smul_eq_mul]
  rw [lt_div_iff₀ h3L] at h2
  calc |aux_cd_F G lam K t' - aux_cd_F G lam K t - (t' - t) * Hfun G lam K t|
      ≤ 3 * L * (t' - t) ^ 2 := hq
    _ = (3 * L * |t' - t|) * |t' - t| := by rw [← sq_abs (t' - t)]; ring
    _ ≤ c * |t' - t| := by
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      linarith

lemma aux_cd_F_cont (hG : aux_cd_Good G) (lam K : ℝ) : Continuous (aux_cd_F G lam K) := by
  have hρ := aux_cd_rho_cont hG lam K
  have hΦ := aux_cd_Phi_cont hG
  show Continuous fun t => aux_cd_Phi G (aux_cd_rho G lam K t + t) -
    aux_cd_Phi G (aux_cd_rho G lam K t)
  exact (hΦ.comp (hρ.add continuous_id)).sub (hΦ.comp hρ)

lemma aux_cd_intH (hG : aux_cd_Good G) (lam K : ℝ) {Q : ℝ} (hQ : 0 < Q) :
    ∫ y in (0 : ℝ)..Q, Hfun G lam K y = aux_cd_F G lam K Q := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hQ.le
    (aux_cd_F_cont hG lam K).continuousOn (fun x hx => aux_cd_F_deriv hG lam K hx.1)
    ((aux_cd_H_cont hG lam K).intervalIntegrable _ _)]
  have h0 : aux_cd_F G lam K 0 = 0 := by simp [aux_cd_F]
  rw [h0, sub_zero]

lemma aux_cd_C_eq (hG : aux_cd_Good G) (lam K : ℝ) {Q : ℝ} (hQ : 0 < Q) :
    Cfun G lam K Q = (lam * K + aux_cd_F G lam K Q) / Q := by
  unfold Cfun qrCost aux_cd_F
  rw [aux_cd_int_eq hG]
  have : aux_cd_rho G lam K Q = reorderPt G lam K Q := by simp [aux_cd_rho, hQ]
  rw [this]

lemma aux_cd_part1 (hG : aux_cd_Good G) (lam K : ℝ) {Q : ℝ} (hQ : 0 < Q) :
    Cfun G lam K Q = G (idealPt G) + C0fun G lam K Q := by
  rw [aux_cd_C_eq hG lam K hQ]
  unfold C0fun H0fun
  rw [intervalIntegral.integral_sub ((aux_cd_H_cont hG lam K).intervalIntegrable _ _)
    intervalIntegrable_const, aux_cd_intH hG lam K hQ, intervalIntegral.integral_const,
    smul_eq_mul, sub_zero]
  field_simp
  ring

lemma aux_cd_part2 (hG : aux_cd_Good G) (lam K : ℝ) {Qs : ℝ} (hopt : IsOptQty G lam K Qs) :
    H0fun G lam K Qs = C0fun G lam K Qs := by
  obtain ⟨hQs, hle⟩ := hopt
  have hC := aux_cd_part1 hG lam K hQs
  have key : Hfun G lam K Qs = Cfun G lam K Qs := by
    have hd : HasDerivAt (fun Q => (lam * K + aux_cd_F G lam K Q) / Q)
        ((Hfun G lam K Qs * Qs - (lam * K + aux_cd_F G lam K Qs) * 1) / Qs ^ 2) Qs :=
      ((aux_cd_F_deriv hG lam K hQs).const_add (lam * K)).div (hasDerivAt_id' Qs) hQs.ne'
    have hloc : IsLocalMin (fun Q => (lam * K + aux_cd_F G lam K Q) / Q) Qs :=
      Filter.eventually_of_mem (Ioi_mem_nhds hQs) fun Q hQ => by
        simp only
        rw [← aux_cd_C_eq hG lam K hQs, ← aux_cd_C_eq hG lam K hQ]
        exact hle Q hQ
    have h0 := hloc.hasDerivAt_eq_zero hd
    rw [div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · rw [aux_cd_C_eq hG lam K hQs, eq_div_iff hQs.ne']; linarith
    · exact absurd h0 (pow_ne_zero 2 hQs.ne')
  unfold H0fun; rw [key, hC]; ring

end Abstract

lemma aux_cd_good (M : QRModel) : aux_cd_Good M.G := by
  have := M.isProb
  exact ⟨⟨M.h + M.p, by linarith [M.h_pos, M.p_pos],
      aux_cd_lip M.integrable_id M.h_pos M.p_pos⟩,
    aux_cd_conv M.integrable_id M.h_pos M.p_pos,
    ⟨M.h, M.p, ∫ x, x ∂M.μ, M.h_pos, M.p_pos, aux_cd_coer M.integrable_id M.h_pos M.p_pos⟩,
    M.unique_min⟩

end ZhengQR.CostBounds

open ZhengQR.CostBounds

theorem solution (M : QRModel) :
    (∀ Q : ℝ, 0 < Q →
      Cfun M.G M.lam M.K Q = M.G (idealPt M.G) + C0fun M.G M.lam M.K Q) ∧
    (∀ Qs : ℝ, IsOptQty M.G M.lam M.K Qs →
      H0fun M.G M.lam M.K Qs = C0fun M.G M.lam M.K Qs) :=
  ⟨fun _ hQ => aux_cd_part1 (aux_cd_good M) M.lam M.K hQ,
   fun _ h => aux_cd_part2 (aux_cd_good M) M.lam M.K h⟩
