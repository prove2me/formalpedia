-- Prove2me | solution 1 for ZhengQR.CostBounds.optimal_cost_bounds
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T23:06:07.70649+00:00
-- url     : https://prove2.me/submissions/9c5eb7b1-2620-42d7-9760-b9ad4161c330

import Mathlib
import Definitions.Def_ZhengQR_CostBounds_QRMachinery
import Definitions.Def_ZhengQR_CostBounds_Model
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_costCurves
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel



namespace ZhengQR.CostBounds
end ZhengQR.CostBounds
section

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

namespace ZhengQR.CostBounds
theorem ocb_cost_decomposition (M : QRModel) :
    (∀ Q : ℝ, 0 < Q →
      Cfun M.G M.lam M.K Q = M.G (idealPt M.G) + C0fun M.G M.lam M.K Q) ∧
    (∀ Qs : ℝ, IsOptQty M.G M.lam M.K Qs →
      H0fun M.G M.lam M.K Qs = C0fun M.G M.lam M.K Qs) :=
  ⟨fun _ hQ => aux_cd_part1 (aux_cd_good M) M.lam M.K hQ,
   fun _ h => aux_cd_part2 (aux_cd_good M) M.lam M.K h⟩

end ZhengQR.CostBounds
end

section

namespace ZhengQR.CostBounds

/-- Antiderivative of the EOQ inventory-cost rate. -/
noncomputable def aux_eoqopt_Psi (a h p : ℝ) (y : ℝ) : ℝ :=
  h / 2 * (max (y - a) 0) ^ 2 - p / 2 * (max (a - y) 0) ^ 2

lemma aux_eoqopt_cont (lam L h p : ℝ) : Continuous (eoqInvCost lam L h p) := by
  unfold eoqInvCost
  fun_prop

lemma aux_eoqopt_Psi_cont (a h p : ℝ) : Continuous (aux_eoqopt_Psi a h p) := by
  unfold aux_eoqopt_Psi
  fun_prop

lemma aux_eoqopt_hasDeriv (lam L h p : ℝ) (y : ℝ) :
    HasDerivAt (aux_eoqopt_Psi (lam * L) h p) (eoqInvCost lam L h p y) y := by
  apply hasDerivAt_of_hasDerivAt_of_ne' (x := lam * L)
  · intro z hz
    rcases lt_or_gt_of_ne hz with hlt | hgt
    · have hev : aux_eoqopt_Psi (lam * L) h p =ᶠ[nhds z]
          fun w => -(p / 2) * (lam * L - w) ^ 2 := by
        filter_upwards [eventually_lt_nhds hlt] with w hw
        simp only [aux_eoqopt_Psi]
        rw [max_eq_right (by linarith : w - lam * L ≤ 0),
          max_eq_left (by linarith : 0 ≤ lam * L - w)]
        ring
      have hd : HasDerivAt (fun w => -(p / 2) * (lam * L - w) ^ 2)
          (eoqInvCost lam L h p z) z := by
        refine ((((hasDerivAt_id z).const_sub (lam * L)).pow 2).const_mul (-(p / 2))).congr_deriv ?_
        simp only [eoqInvCost, id]
        rw [max_eq_right (by linarith : z - lam * L ≤ 0),
          max_eq_left (by linarith : 0 ≤ lam * L - z)]
        push_cast
        ring
      exact hd.congr_of_eventuallyEq hev
    · have hev : aux_eoqopt_Psi (lam * L) h p =ᶠ[nhds z]
          fun w => (h / 2) * (w - lam * L) ^ 2 := by
        filter_upwards [eventually_gt_nhds hgt] with w hw
        simp only [aux_eoqopt_Psi]
        rw [max_eq_left (by linarith : 0 ≤ w - lam * L),
          max_eq_right (by linarith : lam * L - w ≤ 0)]
        ring
      have hd : HasDerivAt (fun w => (h / 2) * (w - lam * L) ^ 2)
          (eoqInvCost lam L h p z) z := by
        refine ((((hasDerivAt_id z).sub_const (lam * L)).pow 2).const_mul (h / 2)).congr_deriv ?_
        simp only [eoqInvCost, id]
        rw [max_eq_left (by linarith : 0 ≤ z - lam * L),
          max_eq_right (by linarith : lam * L - z ≤ 0)]
        push_cast
        ring
      exact hd.congr_of_eventuallyEq hev
  · exact (aux_eoqopt_Psi_cont _ _ _).continuousAt
  · exact (aux_eoqopt_cont _ _ _ _).continuousAt

lemma aux_eoqopt_integral (lam L h p s t : ℝ) :
    ∫ y in s..t, eoqInvCost lam L h p y
      = aux_eoqopt_Psi (lam * L) h p t - aux_eoqopt_Psi (lam * L) h p s :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => aux_eoqopt_hasDeriv lam L h p y)
    ((aux_eoqopt_cont lam L h p).intervalIntegrable s t)

lemma aux_eoqopt_Fbound (a h p Q r : ℝ) (hh : 0 < h) (hp : 0 < p) (hQ : 0 < Q) :
    h * p * Q ^ 2 / 2 ≤ (h + p) * (aux_eoqopt_Psi a h p (r + Q) - aux_eoqopt_Psi a h p r) ∧
    ((h + p) * (aux_eoqopt_Psi a h p (r + Q) - aux_eoqopt_Psi a h p r) = h * p * Q ^ 2 / 2 →
      (h + p) * (r - a) + h * Q = 0) := by
  unfold aux_eoqopt_Psi
  rcases le_total 0 (r - a) with hu | hu
  · rw [max_eq_left (by linarith : 0 ≤ r + Q - a), max_eq_right (by linarith : a - (r + Q) ≤ 0),
      max_eq_left hu, max_eq_right (by linarith : a - r ≤ 0)]
    have key : (h + p) * (h / 2 * (r + Q - a) ^ 2 - p / 2 * 0 ^ 2 - (h / 2 * (r - a) ^ 2 - p / 2 * 0 ^ 2))
        - h * p * Q ^ 2 / 2 = (h + p) * h * (r - a) * Q + h ^ 2 * Q ^ 2 / 2 := by ring
    have h1 : 0 ≤ (h + p) * h * (r - a) * Q := by positivity
    have h2 : 0 < h ^ 2 * Q ^ 2 / 2 := by positivity
    constructor
    · linarith
    · intro heq; exfalso; linarith
  · rcases le_total 0 (r + Q - a) with hv | hv
    · rw [max_eq_left hv, max_eq_right (by linarith : a - (r + Q) ≤ 0),
        max_eq_right hu, max_eq_left (by linarith : 0 ≤ a - r)]
      have key : (h + p) * (h / 2 * (r + Q - a) ^ 2 - p / 2 * 0 ^ 2 - (h / 2 * 0 ^ 2 - p / 2 * (a - r) ^ 2))
          - h * p * Q ^ 2 / 2 = ((h + p) * (r - a) + h * Q) ^ 2 / 2 := by ring
      have h1 : 0 ≤ ((h + p) * (r - a) + h * Q) ^ 2 := sq_nonneg _
      constructor
      · linarith
      · intro heq
        have h2 : ((h + p) * (r - a) + h * Q) ^ 2 = 0 := by linarith
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    · rw [max_eq_right hv, max_eq_left (by linarith : 0 ≤ a - (r + Q)),
        max_eq_right hu, max_eq_left (by linarith : 0 ≤ a - r)]
      have key : (h + p) * (h / 2 * 0 ^ 2 - p / 2 * (a - (r + Q)) ^ 2 - (h / 2 * 0 ^ 2 - p / 2 * (a - r) ^ 2))
          - h * p * Q ^ 2 / 2 = (h + p) * p * (-(r + Q - a)) * Q + p ^ 2 * Q ^ 2 / 2 := by ring
      have h0 : 0 ≤ -(r + Q - a) := by linarith
      have h1 : 0 ≤ (h + p) * p * (-(r + Q - a)) * Q := by positivity
      have h2 : 0 < p ^ 2 * Q ^ 2 / 2 := by positivity
      constructor
      · linarith
      · intro heq; exfalso; linarith

lemma aux_eoqopt_Fval (a h p Q : ℝ) (hh : 0 < h) (hp : 0 < p) (hQ : 0 < Q) :
    aux_eoqopt_Psi a h p (a - h * Q / (h + p) + Q) - aux_eoqopt_Psi a h p (a - h * Q / (h + p))
      = h * p / (h + p) * Q ^ 2 / 2 := by
  have hhp : 0 < h + p := by linarith
  have e1 : a - h * Q / (h + p) + Q - a = p * Q / (h + p) := by field_simp; ring
  have e2 : a - (a - h * Q / (h + p) + Q) = -(p * Q / (h + p)) := by field_simp; ring
  have e3 : a - h * Q / (h + p) - a = -(h * Q / (h + p)) := by ring
  have e4 : a - (a - h * Q / (h + p)) = h * Q / (h + p) := by ring
  have p1 : 0 ≤ p * Q / (h + p) := by positivity
  have p2 : 0 ≤ h * Q / (h + p) := by positivity
  unfold aux_eoqopt_Psi
  rw [e1, e2, e3, e4, max_eq_left p1, max_eq_right (by linarith : -(p * Q / (h + p)) ≤ 0),
    max_eq_right (by linarith : -(h * Q / (h + p)) ≤ 0), max_eq_left p2]
  field_simp
  ring

end ZhengQR.CostBounds

open ZhengQR.CostBounds

namespace ZhengQR.CostBounds
theorem ocb_eoq_optimum (M : QRModel) :
    (∀ Q : ℝ, 0 ≤ Q → Hfun M.Gd M.lam M.K Q = M.h * M.p / (M.h + M.p) * Q) ∧
    (∀ Q : ℝ, IsOptQty M.Gd M.lam M.K Q ↔ Q = M.Qd) ∧
    Cfun M.Gd M.lam M.K M.Qd = Hfun M.Gd M.lam M.K M.Qd := by
  have hlam := M.lam_pos
  have hK := M.K_pos
  have hh := M.h_pos
  have hp := M.p_pos
  have hhp : 0 < M.h + M.p := by linarith
  have hqr : ∀ Q r : ℝ, qrCost M.Gd M.lam M.K Q r
      = (M.lam * M.K + (aux_eoqopt_Psi (M.lam * M.L) M.h M.p (r + Q)
          - aux_eoqopt_Psi (M.lam * M.L) M.h M.p r)) / Q := by
    intro Q r
    simp only [qrCost, QRModel.Gd]
    rw [aux_eoqopt_integral]
  have hr0 : ∀ Q : ℝ, 0 < Q →
      reorderPt M.Gd M.lam M.K Q = M.lam * M.L - M.h * Q / (M.h + M.p) := by
    intro Q hQ
    have hval := aux_eoqopt_Fval (M.lam * M.L) M.h M.p Q hh hp hQ
    have hopt : IsOptReorder M.Gd M.lam M.K Q (M.lam * M.L - M.h * Q / (M.h + M.p)) := by
      intro r'
      rw [hqr, hqr]
      apply div_le_div_of_nonneg_right _ hQ.le
      have h1 := (aux_eoqopt_Fbound (M.lam * M.L) M.h M.p Q r' hh hp hQ).1
      rw [hval]
      have h2 : M.h * M.p / (M.h + M.p) * Q ^ 2 / 2 * (M.h + M.p) = M.h * M.p * Q ^ 2 / 2 := by
        field_simp
      nlinarith
    have hex : ∃ r, IsOptReorder M.Gd M.lam M.K Q r := ⟨_, hopt⟩
    unfold reorderPt
    rw [dif_pos hex]
    have hc := hex.choose_spec (M.lam * M.L - M.h * Q / (M.h + M.p))
    rw [hqr, hqr] at hc
    have hc' := (div_le_div_iff_of_pos_right hQ).mp hc
    have hb := aux_eoqopt_Fbound (M.lam * M.L) M.h M.p Q hex.choose hh hp hQ
    rw [hval] at hc'
    have h2 : M.h * M.p / (M.h + M.p) * Q ^ 2 / 2 * (M.h + M.p) = M.h * M.p * Q ^ 2 / 2 := by
      field_simp
    have heq : (M.h + M.p) * (aux_eoqopt_Psi (M.lam * M.L) M.h M.p (hex.choose + Q)
        - aux_eoqopt_Psi (M.lam * M.L) M.h M.p hex.choose) = M.h * M.p * Q ^ 2 / 2 := by
      apply le_antisymm _ hb.1
      nlinarith
    have hlin := hb.2 heq
    field_simp
    linarith
  -- values of H
  have hH : ∀ Q : ℝ, 0 ≤ Q → Hfun M.Gd M.lam M.K Q = M.h * M.p / (M.h + M.p) * Q := by
    intro Q hQ
    rcases hQ.lt_or_eq with hQ | hQ
    · unfold Hfun
      rw [if_pos hQ, hr0 Q hQ]
      simp only [QRModel.Gd, eoqInvCost]
      have p2 : 0 ≤ M.h * Q / (M.h + M.p) := by positivity
      rw [max_eq_right (by linarith : M.lam * M.L - M.h * Q / (M.h + M.p) - M.lam * M.L ≤ 0),
        max_eq_left (by linarith : 0 ≤ M.lam * M.L - (M.lam * M.L - M.h * Q / (M.h + M.p)))]
      field_simp
      ring
    · subst hQ
      unfold Hfun
      rw [if_neg (lt_irrefl 0)]
      have hnn : ∀ y, 0 ≤ M.Gd y := by
        intro y
        simp only [QRModel.Gd, eoqInvCost]
        have := le_max_right (y - M.lam * M.L) 0
        have := le_max_right (M.lam * M.L - y) 0
        positivity
      have hzero : M.Gd (M.lam * M.L) = 0 := by
        simp [QRModel.Gd, eoqInvCost]
      have hex : ∃ y, ∀ z, M.Gd y ≤ M.Gd z := ⟨M.lam * M.L, fun z => by rw [hzero]; exact hnn z⟩
      unfold idealPt
      rw [dif_pos hex]
      have := hex.choose_spec (M.lam * M.L)
      rw [hzero] at this
      have := hnn hex.choose
      simp only [mul_zero]
      linarith
  -- values of C
  have hC : ∀ Q : ℝ, 0 < Q →
      Cfun M.Gd M.lam M.K Q = (M.lam * M.K + M.h * M.p / (M.h + M.p) * Q ^ 2 / 2) / Q := by
    intro Q hQ
    unfold Cfun
    rw [hr0 Q hQ, hqr, aux_eoqopt_Fval _ _ _ _ hh hp hQ]
  -- properties of Qd
  set c := M.h * M.p / (M.h + M.p) with hc_def
  have hc : 0 < c := by positivity
  have hQd_pos : 0 < M.Qd := by
    unfold QRModel.Qd eoqQty
    apply Real.sqrt_pos.mpr
    positivity
  have hQd_sq : M.Qd ^ 2 = 2 * M.lam * M.K * (M.h + M.p) / (M.h * M.p) := by
    unfold QRModel.Qd eoqQty
    rw [Real.sq_sqrt]
    positivity
  have hkey : M.lam * M.K = c * M.Qd ^ 2 / 2 := by
    rw [hQd_sq, hc_def]
    field_simp
  refine ⟨hH, ?_, ?_⟩
  · intro Q
    constructor
    · rintro ⟨hQ, hall⟩
      have h1 := hall M.Qd hQd_pos
      rw [hC Q hQ, hC M.Qd hQd_pos, hkey, div_le_div_iff₀ hQ hQd_pos] at h1
      have h2 : c * M.Qd * (Q - M.Qd) ^ 2 ≤ 0 := by nlinarith
      have h3 : 0 < c * M.Qd := by positivity
      have h4 : (Q - M.Qd) ^ 2 ≤ 0 := by
        by_contra hne
        push Not at hne
        have := mul_pos h3 hne
        linarith
      have h5 : (Q - M.Qd) ^ 2 = 0 := le_antisymm h4 (sq_nonneg _)
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h5
      linarith
    · rintro rfl
      refine ⟨hQd_pos, fun Q' hQ' => ?_⟩
      rw [hC _ hQd_pos, hC Q' hQ', hkey, div_le_div_iff₀ hQd_pos hQ']
      have h3 : 0 ≤ c * M.Qd * (Q' - M.Qd) ^ 2 := by positivity
      nlinarith
  · rw [hC _ hQd_pos, hH _ hQd_pos.le, hkey]
    field_simp
    ring

end ZhengQR.CostBounds
end

section
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic

lemma aux_hfp_int {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (y : ℝ) :
    Integrable (fun x : ℝ => h * max (y - x) 0 + p * max (x - y) 0) μ := by
  have := hM.isProb
  have hi := hM.integrable
  have h1 : Integrable (fun x : ℝ => max (y - x) 0) μ :=
    ((integrable_const y).sub hi).sup (integrable_zero _ _ _)
  have h2 : Integrable (fun x : ℝ => max (x - y) 0) μ :=
    (hi.sub (integrable_const y)).sup (integrable_zero _ _ _)
  exact (h1.const_mul h).add (h2.const_mul p)

lemma aux_hfp_lip_up {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) {y z : ℝ}
    (hyz : y ≤ z) : newsvendorCost μ h p z - newsvendorCost μ h p y ≤ h * (z - y) := by
  have := hM.isProb
  unfold newsvendorCost
  rw [← integral_sub (aux_hfp_int hM z) (aux_hfp_int hM y)]
  have : ∫ x, (h * (z - y)) ∂μ = h * (z - y) := by simp
  rw [← this]
  apply integral_mono ((aux_hfp_int hM z).sub (aux_hfp_int hM y)) (integrable_const _)
  intro x
  have hh := hM.h_pos.le
  have hp := hM.p_pos.le
  simp only [Pi.sub_apply, Pi.add_apply] at *
  have e1 : max (z - x) 0 - max (y - x) 0 ≤ z - y := by
    rcases le_total (z - x) 0 with h1 | h1 <;> rcases le_total (y - x) 0 with h2 | h2 <;>
      simp [*] <;> linarith
  have e2 : max (x - z) 0 - max (x - y) 0 ≤ 0 := by
    rcases le_total (x - z) 0 with h1 | h1 <;> rcases le_total (x - y) 0 with h2 | h2 <;>
      simp [*] <;> linarith
  nlinarith [mul_le_mul_of_nonneg_left e1 hh, mul_le_mul_of_nonneg_left e2 hp]

lemma aux_hfp_lip_dn {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) {y z : ℝ}
    (hyz : y ≤ z) : newsvendorCost μ h p y - newsvendorCost μ h p z ≤ p * (z - y) := by
  have := hM.isProb
  unfold newsvendorCost
  rw [← integral_sub (aux_hfp_int hM y) (aux_hfp_int hM z)]
  have : ∫ x, (p * (z - y)) ∂μ = p * (z - y) := by simp
  rw [← this]
  apply integral_mono ((aux_hfp_int hM y).sub (aux_hfp_int hM z)) (integrable_const _)
  intro x
  have hh := hM.h_pos.le
  have hp := hM.p_pos.le
  simp only [Pi.sub_apply, Pi.add_apply] at *
  have e1 : max (y - x) 0 - max (z - x) 0 ≤ 0 := by
    rcases le_total (z - x) 0 with h1 | h1 <;> rcases le_total (y - x) 0 with h2 | h2 <;>
      simp [*] <;> linarith
  have e2 : max (x - y) 0 - max (x - z) 0 ≤ z - y := by
    rcases le_total (x - z) 0 with h1 | h1 <;> rcases le_total (x - y) 0 with h2 | h2 <;>
      simp [*] <;> linarith
  nlinarith [mul_le_mul_of_nonneg_left e1 hh, mul_le_mul_of_nonneg_left e2 hp]

lemma aux_hfp_lb1 {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (y : ℝ) :
    p * (lam * L - y) ≤ newsvendorCost μ h p y := by
  have := hM.isProb
  unfold newsvendorCost
  have : ∫ x, p * (x - y) ∂μ = p * (lam * L - y) := by
    rw [integral_const_mul, integral_sub hM.integrable (integrable_const y), hM.mean]
    simp
  rw [← this]
  apply integral_mono ((hM.integrable.sub (integrable_const y)).const_mul p) (aux_hfp_int hM y)
  intro x
  have hh := hM.h_pos.le
  have hp := hM.p_pos.le
  simp only [Pi.sub_apply, Pi.add_apply] at *
  nlinarith [le_max_left (x - y) 0, le_max_right (y - x) 0,
    mul_le_mul_of_nonneg_left (le_max_left (x - y) 0) hp,
    mul_nonneg hh (le_max_right (y - x) 0)]

lemma aux_hfp_lb2 {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (y : ℝ) :
    h * (y - lam * L) ≤ newsvendorCost μ h p y := by
  have := hM.isProb
  unfold newsvendorCost
  have : ∫ x, h * (y - x) ∂μ = h * (y - lam * L) := by
    rw [integral_const_mul, integral_sub (integrable_const y) hM.integrable, hM.mean]
    simp
  rw [← this]
  apply integral_mono (((integrable_const y).sub hM.integrable).const_mul h) (aux_hfp_int hM y)
  intro x
  have hh := hM.h_pos.le
  have hp := hM.p_pos.le
  simp only [Pi.sub_apply, Pi.add_apply] at *
  nlinarith [mul_le_mul_of_nonneg_left (le_max_left (y - x) 0) hh,
    mul_nonneg hp (le_max_right (x - y) 0)]

lemma aux_hfp_convex {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) :
    ConvexOn ℝ Set.univ (newsvendorCost μ h p) := by
  have := hM.isProb
  refine ⟨convex_univ, fun y _ z _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  unfold newsvendorCost
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((aux_hfp_int hM y).const_mul a) ((aux_hfp_int hM z).const_mul b)]
  apply integral_mono (aux_hfp_int hM _)
    (((aux_hfp_int hM y).const_mul a).add ((aux_hfp_int hM z).const_mul b))
  intro x
  have hh := hM.h_pos.le
  have hp := hM.p_pos.le
  simp only [Pi.sub_apply, Pi.add_apply] at *
  have e1 : max (a * y + b * z - x) 0 ≤ a * max (y - x) 0 + b * max (z - x) 0 := by
    apply max_le
    · have : a * y + b * z - x = a * (y - x) + b * (z - x) := by linear_combination x * hab
      rw [this]
      nlinarith [mul_le_mul_of_nonneg_left (le_max_left (y - x) 0) ha,
        mul_le_mul_of_nonneg_left (le_max_left (z - x) 0) hb]
    · nlinarith [mul_nonneg ha (le_max_right (y - x) 0), mul_nonneg hb (le_max_right (z - x) 0)]
  have e2 : max (x - (a * y + b * z)) 0 ≤ a * max (x - y) 0 + b * max (x - z) 0 := by
    apply max_le
    · have : x - (a * y + b * z) = a * (x - y) + b * (x - z) := by linear_combination (-x) * hab
      rw [this]
      nlinarith [mul_le_mul_of_nonneg_left (le_max_left (x - y) 0) ha,
        mul_le_mul_of_nonneg_left (le_max_left (x - z) 0) hb]
    · nlinarith [mul_nonneg ha (le_max_right (x - y) 0), mul_nonneg hb (le_max_right (x - z) 0)]
  nlinarith [mul_le_mul_of_nonneg_left e1 hh, mul_le_mul_of_nonneg_left e2 hp]

lemma aux_hfp_cont {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) :
    Continuous (newsvendorCost μ h p) := by
  have hh := hM.h_pos.le
  have hp := hM.p_pos.le
  refine (LipschitzWith.of_dist_le_mul (K := ⟨h + p, by positivity⟩) fun x y => ?_).continuous
  simp only [Real.dist_eq]
  change |newsvendorCost μ h p x - newsvendorCost μ h p y| ≤ (h + p) * |x - y|
  rcases le_total x y with hxy | hxy
  · have e1 := aux_hfp_lip_up hM hxy
    have e2 := aux_hfp_lip_dn hM hxy
    rw [abs_sub_comm x y, abs_of_nonneg (by linarith : 0 ≤ y - x), abs_sub_le_iff]
    constructor <;> nlinarith
  · have e1 := aux_hfp_lip_up hM hxy
    have e2 := aux_hfp_lip_dn hM hxy
    rw [abs_of_nonneg (by linarith : 0 ≤ x - y), abs_sub_le_iff]
    constructor <;> nlinarith

section generic
variable {G : ℝ → ℝ} {y0 : ℝ}

lemma aux_hfp_smono (hconv : ConvexOn ℝ Set.univ G) (hmin : ∀ z, G y0 ≤ G z)
    (huniq : ∀ y, (∀ z, G y ≤ G z) → y = y0) : StrictMonoOn G (Set.Ici y0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ici] at ha hb
  have hlt : G y0 < G b := by
    refine lt_of_le_of_ne (hmin b) (fun e => ?_)
    have := huniq b (fun z => e ▸ hmin z)
    linarith
  have hby : 0 < b - y0 := by linarith
  set t := (b - a) / (b - y0) with ht
  have ht0 : 0 < t := div_pos (by linarith) hby
  have ht1 : 0 ≤ 1 - t := by
    rw [ht, sub_nonneg, div_le_one hby]; linarith
  have hc := hconv.2 (Set.mem_univ y0) (Set.mem_univ b) ht0.le ht1 (by ring)
  simp only [smul_eq_mul] at hc
  have e : t * y0 + (1 - t) * b = a := by
    rw [ht]; field_simp; ring
  rw [e] at hc
  nlinarith

lemma aux_hfp_santi (hconv : ConvexOn ℝ Set.univ G) (hmin : ∀ z, G y0 ≤ G z)
    (huniq : ∀ y, (∀ z, G y ≤ G z) → y = y0) : StrictAntiOn G (Set.Iic y0) := by
  intro a ha b hb hab
  simp only [Set.mem_Iic] at ha hb
  have hlt : G y0 < G a := by
    refine lt_of_le_of_ne (hmin a) (fun e => ?_)
    have := huniq a (fun z => e ▸ hmin z)
    linarith
  have hby : 0 < y0 - a := by linarith
  set t := (b - a) / (y0 - a) with ht
  have ht0 : 0 < t := div_pos (by linarith) hby
  have ht1 : 0 ≤ 1 - t := by
    rw [ht, sub_nonneg, div_le_one hby]; linarith
  have hc := hconv.2 (Set.mem_univ y0) (Set.mem_univ a) ht0.le ht1 (by ring)
  simp only [smul_eq_mul] at hc
  have e : t * y0 + (1 - t) * a = b := by
    rw [ht]; field_simp; ring
  rw [e] at hc
  nlinarith

lemma aux_hfp_qr_deriv (hGc : Continuous G) (lam K Q r : ℝ) :
    HasDerivAt (fun r => qrCost G lam K Q r) ((G (r + Q) - G r) / Q) r := by
  have hF : ∀ u, HasDerivAt (fun u => ∫ x in (0:ℝ)..u, G x) (G u) u :=
    fun u => (hGc.integral_hasStrictDerivAt 0 u).hasDerivAt
  have e : (fun r => qrCost G lam K Q r) =
      fun r => (lam * K + ((∫ x in (0:ℝ)..(r + Q), G x) - ∫ x in (0:ℝ)..r, G x)) / Q := by
    funext r
    unfold qrCost
    rw [intervalIntegral.integral_interval_sub_left (hGc.intervalIntegrable _ _)
      (hGc.intervalIntegrable _ _)]
  rw [e]
  have h1 : HasDerivAt (fun r => ∫ x in (0:ℝ)..(r + Q), G x) (G (r + Q)) r :=
    HasDerivAt.comp_add_const r Q (hF (r + Q))
  exact ((h1.sub (hF r)).const_add (lam * K)).div_const Q

lemma aux_hfp_opt_eq (hGc : Continuous G) {lam K Q r : ℝ} (hQ : 0 < Q)
    (hr : IsOptReorder G lam K Q r) : G r = G (r + Q) := by
  have hloc : IsLocalMin (fun r => qrCost G lam K Q r) r := Filter.Eventually.of_forall hr
  have := hloc.hasDerivAt_eq_zero (aux_hfp_qr_deriv hGc lam K Q r)
  rw [div_eq_zero_iff] at this
  rcases this with h | h <;> linarith

lemma aux_hfp_sides (hsm : StrictMonoOn G (Set.Ici y0)) (hsa : StrictAntiOn G (Set.Iic y0))
    {a Q : ℝ} (hQ : 0 < Q) (ha : G a = G (a + Q)) : a < y0 ∧ y0 < a + Q := by
  constructor
  · by_contra hc
    push Not at hc
    have := hsm (show y0 ≤ a from hc) (show y0 ≤ a + Q by linarith) (by linarith : a < a + Q)
    linarith
  · by_contra hc
    push Not at hc
    have := hsa (show a ≤ y0 by linarith) (show a + Q ≤ y0 from hc) (by linarith : a < a + Q)
    linarith

lemma aux_hfp_psi_pos (hsm : StrictMonoOn G (Set.Ici y0)) (hsa : StrictAntiOn G (Set.Iic y0))
    {a Q : ℝ} (hQ : 0 < Q) (ha : G a = G (a + Q)) {t : ℝ} (ht : a < t) : G t < G (t + Q) := by
  obtain ⟨h1, h2⟩ := aux_hfp_sides hsm hsa hQ ha
  by_cases hty : y0 ≤ t
  · exact hsm (show y0 ≤ t from hty) (show y0 ≤ t + Q by linarith) (by linarith)
  · push Not at hty
    have e1 : G t < G a := hsa (show a ≤ y0 by linarith) (show t ≤ y0 by linarith) ht
    have e2 : G (a + Q) < G (t + Q) :=
      hsm (show y0 ≤ a + Q by linarith) (show y0 ≤ t + Q by linarith) (by linarith)
    linarith

lemma aux_hfp_psi_neg (hsm : StrictMonoOn G (Set.Ici y0)) (hsa : StrictAntiOn G (Set.Iic y0))
    {a Q : ℝ} (hQ : 0 < Q) (ha : G a = G (a + Q)) {t : ℝ} (ht : t < a) : G (t + Q) < G t := by
  obtain ⟨h1, h2⟩ := aux_hfp_sides hsm hsa hQ ha
  by_cases hty : t + Q ≤ y0
  · exact hsa (show t ≤ y0 by linarith) (show t + Q ≤ y0 from hty) (by linarith)
  · push Not at hty
    have e1 : G (t + Q) < G (a + Q) :=
      hsm (show y0 ≤ t + Q by linarith) (show y0 ≤ a + Q by linarith) (by linarith)
    have e2 : G a < G t := hsa (show t ≤ y0 by linarith) (show a ≤ y0 by linarith) ht
    linarith

lemma aux_hfp_exists_opt (hGc : Continuous G) (hsm : StrictMonoOn G (Set.Ici y0))
    (hsa : StrictAntiOn G (Set.Iic y0)) {lam K Q : ℝ} (hQ : 0 < Q) :
    ∃ r, IsOptReorder G lam K Q r := by
  have hψc : Continuous (fun t => G (t + Q) - G t) :=
    (hGc.comp (continuous_add_const Q)).sub hGc
  have hlo : G (y0 - Q + Q) - G (y0 - Q) ≤ 0 := by
    rw [sub_add_cancel]
    have := hsa (show y0 - Q ≤ y0 by linarith) (show y0 ≤ y0 from le_refl y0) (by linarith)
    linarith
  have hhi : 0 ≤ G (y0 + Q) - G y0 := by
    have := hsm (show y0 ≤ y0 from le_refl y0) (show y0 ≤ y0 + Q by linarith) (by linarith)
    linarith
  have hmem : (0:ℝ) ∈ Set.Icc ((fun t => G (t + Q) - G t) (y0 - Q))
      ((fun t => G (t + Q) - G t) y0) := ⟨hlo, hhi⟩
  obtain ⟨r0, -, hr0⟩ :=
    intermediate_value_Icc (show y0 - Q ≤ y0 by linarith) hψc.continuousOn hmem
  have hr0' : G r0 = G (r0 + Q) := by
    simp only at hr0
    linarith
  refine ⟨r0, fun r' => ?_⟩
  have hd := aux_hfp_qr_deriv hGc lam K Q
  rcases lt_trichotomy r' r0 with hlt | heq | hgt
  · obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope (fun r => qrCost G lam K Q r)
      (fun r => (G (r + Q) - G r) / Q) hlt
      (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ => hd x)
    have hneg := aux_hfp_psi_neg hsm hsa hQ hr0' hc.2
    have : (G (c + Q) - G c) / Q < 0 := div_neg_of_neg_of_pos (by linarith) hQ
    rw [hc', div_lt_iff₀ (by linarith)] at this
    linarith
  · rw [heq]
  · obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope (fun r => qrCost G lam K Q r)
      (fun r => (G (r + Q) - G r) / Q) hgt
      (fun x _ => (hd x).continuousAt.continuousWithinAt) (fun x _ => hd x)
    have hpos := aux_hfp_psi_pos hsm hsa hQ hr0' hc.1
    have : 0 < (G (c + Q) - G c) / Q := div_pos (by linarith) hQ
    rw [hc', lt_div_iff₀ (by linarith)] at this
    linarith

lemma aux_hfp_reorder_eq (hGc : Continuous G) (hsm : StrictMonoOn G (Set.Ici y0))
    (hsa : StrictAntiOn G (Set.Iic y0)) {lam K Q : ℝ} (hQ : 0 < Q) :
    G (reorderPt G lam K Q) = G (reorderPt G lam K Q + Q) := by
  have hex := aux_hfp_exists_opt hGc hsm hsa (lam := lam) (K := K) hQ
  unfold reorderPt
  rw [dif_pos hex]
  exact aux_hfp_opt_eq hGc hQ hex.choose_spec

lemma aux_hfp_minPt (hmin : ∀ z, G y0 ≤ G z) (huniq : ∀ y, (∀ z, G y ≤ G z) → y = y0) :
    minPt G = y0 := by
  have hex : ∃ y, ∀ z, G y ≤ G z := ⟨y0, hmin⟩
  unfold minPt
  rw [dif_pos hex]
  exact huniq _ hex.choose_spec

lemma aux_hfp_H_pos {lam K Q : ℝ} (hQ : 0 < Q) :
    hFun G lam K Q = G (reorderPt G lam K Q) := by
  unfold hFun; rw [if_pos hQ]

lemma aux_hfp_H_zero {lam K : ℝ} : hFun G lam K 0 = G (minPt G) := by
  unfold hFun; simp

lemma aux_hfp_A (hGc : Continuous G) (hmin : ∀ z, G y0 ≤ G z)
    (huniq : ∀ y, (∀ z, G y ≤ G z) → y = y0) (hsm : StrictMonoOn G (Set.Ici y0))
    (hsa : StrictAntiOn G (Set.Iic y0)) {lam K Q : ℝ} (hQ : 0 ≤ Q) :
    ∃ a, G a = hFun G lam K Q ∧ G (a + Q) = hFun G lam K Q := by
  rcases hQ.eq_or_lt with h0 | hpos
  · subst h0
    refine ⟨y0, ?_, ?_⟩ <;> rw [aux_hfp_H_zero, aux_hfp_minPt hmin huniq] <;> simp
  · refine ⟨reorderPt G lam K Q, ?_, ?_⟩ <;> rw [aux_hfp_H_pos hpos]
    exact (aux_hfp_reorder_eq hGc hsm hsa hpos).symm

lemma aux_hfp_B (hGc : Continuous G) (hmin : ∀ z, G y0 ≤ G z)
    (huniq : ∀ y, (∀ z, G y ≤ G z) → y = y0) (hsm : StrictMonoOn G (Set.Ici y0))
    (hsa : StrictAntiOn G (Set.Iic y0)) {lam K Q : ℝ} (hQ : 0 ≤ Q) (x : ℝ) :
    hFun G lam K Q ≤ max (G x) (G (x + Q)) := by
  rcases hQ.eq_or_lt with h0 | hpos
  · subst h0
    rw [aux_hfp_H_zero, aux_hfp_minPt hmin huniq]
    exact (hmin x).trans (le_max_left _ _)
  · rw [aux_hfp_H_pos hpos]
    have ea := aux_hfp_reorder_eq hGc hsm hsa (lam := lam) (K := K) hpos
    obtain ⟨s1, s2⟩ := aux_hfp_sides hsm hsa hpos ea
    by_cases hc : reorderPt G lam K Q ≤ x
    · rw [ea]
      refine le_trans ?_ (le_max_right _ _)
      exact hsm.monotoneOn (show y0 ≤ reorderPt G lam K Q + Q by linarith)
        (show y0 ≤ x + Q by linarith) (by linarith)
    · push Not at hc
      refine le_trans ?_ (le_max_left _ _)
      exact hsa.antitoneOn (show x ≤ y0 by linarith) (show reorderPt G lam K Q ≤ y0 by linarith)
        hc.le

end generic

end ZhengQR.EOQHeuristic

open ZhengQR.EOQHeuristic

namespace ZhengQR.EOQHeuristic
theorem ocb_hFun_props {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) :
    StrictMonoOn (hFun (newsvendorCost μ h p) lam K) (Set.Ici 0) ∧
    ConvexOn ℝ (Set.Ici 0) (hFun (newsvendorCost μ h p) lam K) ∧
    ContinuousWithinAt (hFun (newsvendorCost μ h p) lam K) (Set.Ici 0) 0 ∧
    (∀ Q Q' : ℝ, 0 ≤ Q → Q < Q' → hFun (newsvendorCost μ h p) lam K Q' - hFun (newsvendorCost μ h p) lam K Q ≤ h * p / (h + p) * (Q' - Q)) ∧
    Tendsto (fun Q : ℝ => hFun (newsvendorCost μ h p) lam K Q / Q) atTop (𝓝 (h * p / (h + p))) := by
  have hh := hM.h_pos
  have hp := hM.p_pos
  have hGc := aux_hfp_cont hM
  have hconv := aux_hfp_convex hM
  obtain ⟨y0, hmin, huniq⟩ := hM.unique_min
  have huniq' : ∀ y, (∀ z, newsvendorCost μ h p y ≤ newsvendorCost μ h p z) → y = y0 :=
    fun y hy => huniq y hy
  have hsm := aux_hfp_smono hconv hmin huniq'
  have hsa := aux_hfp_santi hconv hmin huniq'
  have hA := fun {Q : ℝ} (hQ : 0 ≤ Q) =>
    aux_hfp_A (lam := lam) (K := K) hGc hmin huniq' hsm hsa hQ
  have hB := fun {Q : ℝ} (hQ : 0 ≤ Q) =>
    aux_hfp_B (lam := lam) (K := K) hGc hmin huniq' hsm hsa hQ
  have hH0 : hFun (newsvendorCost μ h p) lam K 0 = newsvendorCost μ h p y0 := by
    rw [aux_hfp_H_zero, aux_hfp_minPt hmin huniq']
  -- slope bound
  have P4 : ∀ Q Q' : ℝ, 0 ≤ Q → Q < Q' → hFun (newsvendorCost μ h p) lam K Q' -
      hFun (newsvendorCost μ h p) lam K Q ≤ h * p / (h + p) * (Q' - Q) := by
    intro Q Q' hQ hQQ'
    obtain ⟨a, ha1, ha2⟩ := hA hQ
    have hd : 0 < Q' - Q := by linarith
    have hs0 : 0 ≤ h * (Q' - Q) / (h + p) := by positivity
    have hsd : h * (Q' - Q) / (h + p) ≤ Q' - Q := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have hBQ := hB (show 0 ≤ Q' by linarith) (a - h * (Q' - Q) / (h + p))
    have e1 := aux_hfp_lip_dn hM (show a - h * (Q' - Q) / (h + p) ≤ a by linarith)
    have e2 := aux_hfp_lip_up hM
      (show a + Q ≤ a - h * (Q' - Q) / (h + p) + Q' by linarith)
    have key1 : p * (a - (a - h * (Q' - Q) / (h + p))) = h * p / (h + p) * (Q' - Q) := by
      field_simp; ring
    have key2 : h * (a - h * (Q' - Q) / (h + p) + Q' - (a + Q)) =
        h * p / (h + p) * (Q' - Q) := by
      field_simp; ring
    have hmax : max (newsvendorCost μ h p (a - h * (Q' - Q) / (h + p)))
        (newsvendorCost μ h p (a - h * (Q' - Q) / (h + p) + Q')) ≤
        hFun (newsvendorCost μ h p) lam K Q + h * p / (h + p) * (Q' - Q) :=
      max_le (by linarith) (by linarith)
    linarith
  -- lower bound
  have hLB : ∀ Q : ℝ, 0 < Q → h * p / (h + p) * Q ≤ hFun (newsvendorCost μ h p) lam K Q := by
    intro Q hQ
    obtain ⟨a, ha1, ha2⟩ := hA hQ.le
    have l1 := aux_hfp_lb1 hM a
    have l2 := aux_hfp_lb2 hM (a + Q)
    rw [ha1] at l1
    rw [ha2] at l2
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  have hge0 : ∀ Q : ℝ, 0 ≤ Q → hFun (newsvendorCost μ h p) lam K 0 ≤
      hFun (newsvendorCost μ h p) lam K Q := by
    intro Q hQ
    obtain ⟨a, ha1, -⟩ := hA hQ
    rw [hH0, ← ha1]
    exact hmin a
  refine ⟨?_, ?_, ?_, P4, ?_⟩
  · -- strict monotonicity
    intro Q hQ Q' hQ' hlt
    simp only [Set.mem_Ici] at hQ hQ'
    have hQ'pos : 0 < Q' := by linarith
    have ea' := aux_hfp_reorder_eq hGc hsm hsa (lam := lam) (K := K) hQ'pos
    obtain ⟨s1', s2'⟩ := aux_hfp_sides hsm hsa hQ'pos ea'
    rw [aux_hfp_H_pos hQ'pos]
    rcases hQ.eq_or_lt with h0 | hpos
    · subst h0
      rw [hH0]
      exact hsa (show reorderPt (newsvendorCost μ h p) lam K Q' ≤ y0 by linarith)
        (show y0 ≤ y0 from le_refl y0) s1'
    · rw [aux_hfp_H_pos hpos]
      have ea := aux_hfp_reorder_eq hGc hsm hsa (lam := lam) (K := K) hpos
      obtain ⟨s1, s2⟩ := aux_hfp_sides hsm hsa hpos ea
      by_cases hc : reorderPt (newsvendorCost μ h p) lam K Q ≤
          reorderPt (newsvendorCost μ h p) lam K Q'
      · rw [ea, ea']
        exact hsm (show y0 ≤ reorderPt (newsvendorCost μ h p) lam K Q + Q by linarith)
          (show y0 ≤ reorderPt (newsvendorCost μ h p) lam K Q' + Q' by linarith) (by linarith)
      · push Not at hc
        exact hsa (show reorderPt (newsvendorCost μ h p) lam K Q' ≤ y0 by linarith)
          (show reorderPt (newsvendorCost μ h p) lam K Q ≤ y0 by linarith) hc
  · -- convexity
    refine ⟨convex_Ici 0, fun Q1 hQ1 Q2 hQ2 s t hs ht hst => ?_⟩
    simp only [Set.mem_Ici] at hQ1 hQ2
    obtain ⟨a1, h11, h12⟩ := hA hQ1
    obtain ⟨a2, h21, h22⟩ := hA hQ2
    simp only [smul_eq_mul]
    have hQnn : 0 ≤ s * Q1 + t * Q2 := by positivity
    have hBQ := hB hQnn (s * a1 + t * a2)
    have c1 := hconv.2 (Set.mem_univ a1) (Set.mem_univ a2) hs ht hst
    have c2 := hconv.2 (Set.mem_univ (a1 + Q1)) (Set.mem_univ (a2 + Q2)) hs ht hst
    simp only [smul_eq_mul] at c1 c2
    have e : s * a1 + t * a2 + (s * Q1 + t * Q2) = s * (a1 + Q1) + t * (a2 + Q2) := by ring
    rw [e] at hBQ
    rw [h11, h21] at c1
    rw [h12, h22] at c2
    exact hBQ.trans (max_le c1 c2)
  · -- continuity at 0
    unfold ContinuousWithinAt
    have hup : Tendsto (fun Q : ℝ => hFun (newsvendorCost μ h p) lam K 0 + h * p / (h + p) * Q)
        (𝓝[Set.Ici 0] 0) (𝓝 (hFun (newsvendorCost μ h p) lam K 0)) := by
      have : Tendsto (fun Q : ℝ => hFun (newsvendorCost μ h p) lam K 0 + h * p / (h + p) * Q)
          (𝓝 0) (𝓝 (hFun (newsvendorCost μ h p) lam K 0 + h * p / (h + p) * 0)) :=
        ((continuous_const.add (continuous_const.mul continuous_id)).tendsto 0)
      rw [mul_zero, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · exact eventually_nhdsWithin_of_forall fun Q hQ => hge0 Q hQ
    · refine eventually_nhdsWithin_of_forall fun Q hQ => ?_
      simp only [Set.mem_Ici] at hQ
      rcases hQ.eq_or_lt with h0 | hpos
      · subst h0; simp
      · have := P4 0 Q le_rfl hpos
        linarith
  · -- asymptotic slope
    have hup : Tendsto (fun Q : ℝ => h * p / (h + p) + hFun (newsvendorCost μ h p) lam K 0 / Q)
        atTop (𝓝 (h * p / (h + p))) := by
      have := (tendsto_const_nhds (x := hFun (newsvendorCost μ h p) lam K 0)).div_atTop
        (tendsto_id (x := (atTop : Filter ℝ)))
      simpa using (tendsto_const_nhds (x := h * p / (h + p))).add this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_gt_atTop 0] with Q hQ
      rw [le_div_iff₀ hQ]
      exact hLB Q hQ
    · filter_upwards [eventually_gt_atTop 0] with Q hQ
      have := P4 0 Q le_rfl hQ
      rw [div_le_iff₀ hQ, add_mul, div_mul_cancel₀ _ hQ.ne']
      linarith

end ZhengQR.EOQHeuristic
end

section
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic

/-- The pointwise cost `h (y - x)⁺ + p (x - y)⁺`. -/
noncomputable def aux_hs_g (h p y x : ℝ) : ℝ := h * max (y - x) 0 + p * max (x - y) 0

lemma aux_hs_g_lb1 {h p : ℝ} (hh : 0 < h) (hp : 0 < p) (y x : ℝ) :
    h * (y - x) ≤ aux_hs_g h p y x := by
  unfold aux_hs_g
  have h1 : y - x ≤ max (y - x) 0 := le_max_left _ _
  have h2 : 0 ≤ max (x - y) 0 := le_max_right _ _
  nlinarith

lemma aux_hs_g_lb2 {h p : ℝ} (hh : 0 < h) (hp : 0 < p) (y x : ℝ) :
    p * (x - y) ≤ aux_hs_g h p y x := by
  unfold aux_hs_g
  have h1 : x - y ≤ max (x - y) 0 := le_max_left _ _
  have h2 : 0 ≤ max (y - x) 0 := le_max_right _ _
  nlinarith

lemma aux_hs_g_sr {h p : ℝ} (hh : 0 < h) (hp : 0 < p) {y z : ℝ} (hyz : y ≤ z) (x : ℝ) :
    aux_hs_g h p z x - aux_hs_g h p y x ≤ h * (z - y) := by
  unfold aux_hs_g
  have h1 : max (z - x) 0 ≤ max (y - x) 0 + (z - y) := by
    apply max_le
    · have := le_max_left (y - x) 0; linarith
    · have := le_max_right (y - x) 0; linarith
  have h2 : max (x - z) 0 ≤ max (x - y) 0 := max_le_max (by linarith) le_rfl
  nlinarith

lemma aux_hs_g_sl {h p : ℝ} (hh : 0 < h) (hp : 0 < p) {y z : ℝ} (hyz : y ≤ z) (x : ℝ) :
    aux_hs_g h p y x - aux_hs_g h p z x ≤ p * (z - y) := by
  unfold aux_hs_g
  have h1 : max (x - y) 0 ≤ max (x - z) 0 + (z - y) := by
    apply max_le
    · have := le_max_left (x - z) 0; linarith
    · have := le_max_right (x - z) 0; linarith
  have h2 : max (y - x) 0 ≤ max (z - x) 0 := max_le_max (by linarith) le_rfl
  nlinarith

lemma aux_hs_max_conv {a b u1 u2 u3 : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hu : (a + b) * u2 = a * u1 + b * u3) :
    (a + b) * max u2 0 ≤ a * max u1 0 + b * max u3 0 := by
  have h1 := le_max_left u1 0
  have h2 := le_max_right u1 0
  have h3 := le_max_left u3 0
  have h4 := le_max_right u3 0
  rcases le_total u2 0 with h | h
  · rw [max_eq_right h]; nlinarith
  · rw [max_eq_left h]; nlinarith

lemma aux_hs_g_conv {h p : ℝ} (hh : 0 < h) (hp : 0 < p) {x1 y z : ℝ} (h1 : x1 < y) (h2 : y < z)
    (t : ℝ) :
    aux_hs_g h p y t * (z - x1) ≤ aux_hs_g h p x1 t * (z - y) + aux_hs_g h p z t * (y - x1) := by
  unfold aux_hs_g
  have e1 := aux_hs_max_conv (a := z - y) (b := y - x1) (u1 := x1 - t) (u2 := y - t) (u3 := z - t)
    (by linarith) (by linarith) (by ring)
  have e2 := aux_hs_max_conv (a := z - y) (b := y - x1) (u1 := t - x1) (u2 := t - y) (u3 := t - z)
    (by linarith) (by linarith) (by ring)
  have e1' := mul_le_mul_of_nonneg_left e1 hh.le
  have e2' := mul_le_mul_of_nonneg_left e2 hp.le
  have : z - y + (y - x1) = z - x1 := by ring
  rw [this] at e1' e2'
  nlinarith

/-- Standing properties of a cost-rate function. -/
structure aux_hs_Good (G : ℝ → ℝ) (h p m : ℝ) : Prop where
  hpos : 0 < h
  ppos : 0 < p
  sr : ∀ y z, y ≤ z → G z - G y ≤ h * (z - y)
  sl : ∀ y z, y ≤ z → G y - G z ≤ p * (z - y)
  conv : ∀ x y z, x < y → y < z → G y * (z - x) ≤ G x * (z - y) + G z * (y - x)
  lb1 : ∀ y, h * (y - m) ≤ G y
  lb2 : ∀ y, p * (m - y) ≤ G y
  umin : ∃! y, ∀ z, G y ≤ G z

lemma aux_hs_eoq_good {lam L h p : ℝ} (hh : 0 < h) (hp : 0 < p) :
    aux_hs_Good (eoqCost lam L h p) h p (lam * L) := by
  have e : ∀ y, eoqCost lam L h p y = aux_hs_g h p y (lam * L) := fun y => rfl
  refine ⟨hh, hp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y z hyz; rw [e, e]; exact aux_hs_g_sr hh hp hyz _
  · intro y z hyz; rw [e, e]; exact aux_hs_g_sl hh hp hyz _
  · intro x y z hxy hyz; rw [e, e, e]; exact aux_hs_g_conv hh hp hxy hyz _
  · intro y; rw [e]; exact aux_hs_g_lb1 hh hp _ _
  · intro y; rw [e]; exact aux_hs_g_lb2 hh hp _ _
  · refine ⟨lam * L, ?_, ?_⟩
    · intro z
      have h0 : eoqCost lam L h p (lam * L) = 0 := by simp [eoqCost]
      rw [h0, e]
      have := aux_hs_g_lb1 hh hp z (lam * L)
      have := aux_hs_g_lb2 hh hp z (lam * L)
      rcases le_total z (lam * L) with hz | hz <;> nlinarith
    · intro y hy
      have h0 : eoqCost lam L h p (lam * L) = 0 := by simp [eoqCost]
      have hy0 := hy (lam * L)
      rw [h0, e] at hy0
      have := aux_hs_g_lb1 hh hp y (lam * L)
      have := aux_hs_g_lb2 hh hp y (lam * L)
      have h3 : y - lam * L ≤ 0 := by nlinarith
      have h4 : lam * L - y ≤ 0 := by nlinarith
      linarith

lemma aux_hs_int {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (y : ℝ) :
    Integrable (fun x => aux_hs_g h p y x) μ := by
  have := hM.isProb
  have hi := hM.integrable
  unfold aux_hs_g
  exact (((integrable_const y).sub hi).pos_part.const_mul h).add
    ((hi.sub (integrable_const y)).pos_part.const_mul p)

lemma aux_hs_int_lin {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (a b : ℝ) :
    ∫ x, (a * x + b) ∂μ = a * (lam * L) + b := by
  have := hM.isProb
  rw [integral_add (hM.integrable.const_mul a) (integrable_const b), integral_const_mul, hM.mean,
    integral_const]
  simp

lemma aux_hs_nv_good {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) :
    aux_hs_Good (newsvendorCost μ h p) h p (lam * L) := by
  have := hM.isProb
  have hh := hM.h_pos
  have hp := hM.p_pos
  have e : ∀ y, newsvendorCost μ h p y = ∫ x, aux_hs_g h p y x ∂μ := fun y => rfl
  refine ⟨hh, hp, ?_, ?_, ?_, ?_, ?_, hM.unique_min⟩
  · intro y z hyz
    rw [e, e, ← integral_sub (aux_hs_int hM z) (aux_hs_int hM y)]
    calc ∫ x, (aux_hs_g h p z x - aux_hs_g h p y x) ∂μ ≤ ∫ x, h * (z - y) ∂μ :=
          integral_mono ((aux_hs_int hM z).sub (aux_hs_int hM y)) (integrable_const _)
            (fun x => aux_hs_g_sr hh hp hyz x)
      _ = h * (z - y) := by simp
  · intro y z hyz
    rw [e, e, ← integral_sub (aux_hs_int hM y) (aux_hs_int hM z)]
    calc ∫ x, (aux_hs_g h p y x - aux_hs_g h p z x) ∂μ ≤ ∫ x, p * (z - y) ∂μ :=
          integral_mono ((aux_hs_int hM y).sub (aux_hs_int hM z)) (integrable_const _)
            (fun x => aux_hs_g_sl hh hp hyz x)
      _ = p * (z - y) := by simp
  · intro x y z hxy hyz
    rw [e, e, e, ← integral_mul_const, ← integral_mul_const, ← integral_mul_const,
      ← integral_add ((aux_hs_int hM x).mul_const _) ((aux_hs_int hM z).mul_const _)]
    exact integral_mono ((aux_hs_int hM y).mul_const _)
      (((aux_hs_int hM x).mul_const _).add ((aux_hs_int hM z).mul_const _))
      (fun t => aux_hs_g_conv hh hp hxy hyz t)
  · intro y
    calc h * (y - lam * L) = ∫ x, ((-h) * x + h * y) ∂μ := by rw [aux_hs_int_lin hM]; ring
      _ ≤ ∫ x, aux_hs_g h p y x ∂μ :=
          integral_mono ((hM.integrable.const_mul _).add (integrable_const _)) (aux_hs_int hM y)
            (fun x => by have := aux_hs_g_lb1 hh hp y x; simp only; linarith)
  · intro y
    calc p * (lam * L - y) = ∫ x, (p * x + (-p * y)) ∂μ := by rw [aux_hs_int_lin hM]; ring
      _ ≤ ∫ x, aux_hs_g h p y x ∂μ :=
          integral_mono ((hM.integrable.const_mul _).add (integrable_const _)) (aux_hs_int hM y)
            (fun x => by have := aux_hs_g_lb2 hh hp y x; simp only; linarith)

section Abstract

variable {G : ℝ → ℝ} {h p m : ℝ}

lemma aux_hs_abs (hG : aux_hs_Good G h p m) (a b : ℝ) :
    |G a - G b| ≤ (h + p) * |a - b| := by
  have hh := hG.hpos; have hp := hG.ppos
  rcases le_total a b with hab | hab
  · have h1 := hG.sr a b hab; have h2 := hG.sl a b hab
    rw [abs_of_nonpos (by linarith : a - b ≤ 0), abs_le]
    constructor <;> nlinarith
  · have h1 := hG.sr b a hab; have h2 := hG.sl b a hab
    rw [abs_of_nonneg (by linarith : 0 ≤ a - b), abs_le]
    constructor <;> nlinarith

lemma aux_hs_cont (hG : aux_hs_Good G h p m) : Continuous G := by
  have hK : 0 ≤ h + p := by linarith [hG.hpos, hG.ppos]
  refine (LipschitzWith.of_dist_le_mul (K := ⟨h + p, hK⟩) fun a b => ?_).continuous
  simp only [Real.dist_eq]
  exact aux_hs_abs hG a b

lemma aux_hs_minPt_spec (hG : aux_hs_Good G h p m) : ∀ z, G (minPt G) ≤ G z := by
  have hex : ∃ y, ∀ z, G y ≤ G z := hG.umin.exists
  have e : minPt G = hex.choose := by unfold minPt; rw [dif_pos hex]
  rw [e]; exact hex.choose_spec

lemma aux_hs_minPt_uniq (hG : aux_hs_Good G h p m) {y : ℝ} (hy : ∀ z, G y ≤ G z) :
    y = minPt G :=
  hG.umin.unique hy (aux_hs_minPt_spec hG)

lemma aux_hs_anti (hG : aux_hs_Good G h p m) {a a' : ℝ} (h1 : a' ≤ a) (h2 : a ≤ minPt G) :
    G a ≤ G a' := by
  have hs := aux_hs_minPt_spec hG
  rcases h1.lt_or_eq with h1 | h1
  · rcases h2.lt_or_eq with h2 | h2
    · have hc := hG.conv a' a (minPt G) h1 h2
      have h3 : G (minPt G) * (a - a') ≤ G a' * (a - a') :=
        mul_le_mul_of_nonneg_right (hs a') (by linarith)
      have h4 : G a * (minPt G - a') ≤ G a' * (minPt G - a') := by nlinarith
      exact le_of_mul_le_mul_right h4 (by linarith)
    · rw [h2]; exact hs a'
  · rw [h1]

lemma aux_hs_mono (hG : aux_hs_Good G h p m) {b b' : ℝ} (h1 : minPt G ≤ b) (h2 : b ≤ b') :
    G b ≤ G b' := by
  have hs := aux_hs_minPt_spec hG
  rcases h2.lt_or_eq with h2 | h2
  · rcases h1.lt_or_eq with h1 | h1
    · have hc := hG.conv (minPt G) b b' h1 h2
      have h3 : G (minPt G) * (b' - b) ≤ G b' * (b' - b) :=
        mul_le_mul_of_nonneg_right (hs b') (by linarith)
      have h4 : G b * (b' - minPt G) ≤ G b' * (b' - minPt G) := by nlinarith
      exact le_of_mul_le_mul_right h4 (by linarith)
    · rw [← h1]; exact hs b'
  · rw [h2]

lemma aux_hs_nonneg (hG : aux_hs_Good G h p m) (y : ℝ) : 0 ≤ G y := by
  have hh := hG.hpos; have hp := hG.ppos
  have h1 := hG.lb1 y; have h2 := hG.lb2 y
  rcases le_total y m with hy | hy <;> nlinarith

lemma aux_hs_exists_opt (hG : aux_hs_Good G h p m) (lam K Q : ℝ) (hQ : 0 < Q) :
    ∃ r, IsOptReorder G lam K Q r := by
  have hh := hG.hpos; have hp := hG.ppos
  have hc := aux_hs_cont hG
  obtain ⟨F, hF⟩ : ∃ F : ℝ → ℝ, F = fun r => ∫ y in r..r + Q, G y := ⟨_, rfl⟩
  have hΦ : ∀ x, HasDerivAt (fun u => ∫ y in (0:ℝ)..u, G y) (G x) x :=
    fun x => (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hΦc : Continuous (fun u => ∫ y in (0:ℝ)..u, G y) :=
    continuous_iff_continuousAt.2 fun x => (hΦ x).continuousAt
  have hFc : Continuous F := by
    have : F = fun r => (∫ y in (0:ℝ)..r + Q, G y) - ∫ y in (0:ℝ)..r, G y := by
      rw [hF]; funext r
      rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _)]
    rw [this]
    exact (hΦc.comp (continuous_add_const Q)).sub hΦc
  have lbA : ∀ r, Q * (h * (r - m)) ≤ F r := by
    intro r
    have := intervalIntegral.integral_mono_on (by linarith : r ≤ r + Q) (intervalIntegrable_const (μ := volume))
      (hc.intervalIntegrable r (r + Q))
      (fun y hy => (show h * (r - m) ≤ G y from by have := hG.lb1 y; nlinarith [hy.1]))
    rw [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] at this
    rw [hF]; exact this
  have lbB : ∀ r, Q * (p * (m - r - Q)) ≤ F r := by
    intro r
    have := intervalIntegral.integral_mono_on (by linarith : r ≤ r + Q) (intervalIntegrable_const (μ := volume))
      (hc.intervalIntegrable r (r + Q))
      (fun y hy => (show p * (m - r - Q) ≤ G y from by have := hG.lb2 y; nlinarith [hy.2]))
    rw [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] at this
    rw [hF]; exact this
  obtain ⟨r0, hr0⟩ : ∃ r, ∀ r', F r ≤ F r' := by
    refine hFc.exists_forall_le' 0 ?_
    rw [cocompact_eq_atBot_atTop, Filter.eventually_sup]
    constructor
    · refine Filter.eventually_atBot.2 ⟨m - Q - |F 0| / (Q * p), fun r hr => ?_⟩
      have h1 : |F 0| / (Q * p) ≤ m - Q - r := by linarith
      rw [div_le_iff₀ (mul_pos hQ hp)] at h1
      have := lbB r
      have := le_abs_self (F 0)
      nlinarith
    · refine Filter.eventually_atTop.2 ⟨m + |F 0| / (Q * h), fun r hr => ?_⟩
      have h1 : |F 0| / (Q * h) ≤ r - m := by linarith
      rw [div_le_iff₀ (mul_pos hQ hh)] at h1
      have := lbA r
      have := le_abs_self (F 0)
      nlinarith
  refine ⟨r0, fun r' => ?_⟩
  have h1 : F r0 ≤ F r' := hr0 r'
  rw [hF] at h1
  unfold qrCost
  exact div_le_div_of_nonneg_right (by simp only at h1; linarith) hQ.le

lemma aux_hs_foc (hG : aux_hs_Good G h p m) (lam K Q r : ℝ) (hQ : 0 < Q)
    (hr : IsOptReorder G lam K Q r) : G (r + Q) = G r := by
  have hc := aux_hs_cont hG
  have hΦ : ∀ x, HasDerivAt (fun u => ∫ y in (0:ℝ)..u, G y) (G x) x :=
    fun x => (hc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have heq : (fun r => qrCost G lam K Q r) =
      fun r => (lam * K + ((∫ y in (0:ℝ)..r + Q, G y) - ∫ y in (0:ℝ)..r, G y)) / Q := by
    funext r; unfold qrCost
    rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
  have hd : HasDerivAt (fun r => qrCost G lam K Q r) ((G (r + Q) - G r) / Q) r := by
    rw [heq]
    exact ((((hΦ (r + Q)).comp_add_const r Q).sub (hΦ r)).const_add (lam * K)).div_const Q
  have hlm : IsLocalMin (fun r => qrCost G lam K Q r) r := Filter.Eventually.of_forall hr
  have := hlm.hasDerivAt_eq_zero hd
  rw [div_eq_zero_iff] at this
  rcases this with h | h
  · linarith
  · exact absurd h hQ.ne'

lemma aux_hs_bracket (hG : aux_hs_Good G h p m) (lam K Q : ℝ) (hQ : 0 ≤ Q) :
    ∃ a b, a ≤ minPt G ∧ minPt G ≤ b ∧ b - a = Q ∧ G a = hFun G lam K Q ∧
      G b = hFun G lam K Q := by
  have hs := aux_hs_minPt_spec hG
  rcases hQ.lt_or_eq with hQ | hQ
  · have hex := aux_hs_exists_opt hG lam K Q hQ
    have hr : IsOptReorder G lam K Q (reorderPt G lam K Q) := by
      unfold reorderPt; rw [dif_pos hex]; exact hex.choose_spec
    have hfoc := aux_hs_foc hG lam K Q _ hQ hr
    have hH : hFun G lam K Q = G (reorderPt G lam K Q) := by unfold hFun; rw [if_pos hQ]
    refine ⟨reorderPt G lam K Q, reorderPt G lam K Q + Q, ?_, ?_, by ring, hH.symm,
      by rw [hH, hfoc]⟩
    · by_contra hcon
      push Not at hcon
      have hc := hG.conv (minPt G) _ _ hcon (by linarith : reorderPt G lam K Q <
        reorderPt G lam K Q + Q)
      rw [hfoc] at hc
      have h1 : G (reorderPt G lam K Q) * Q ≤ G (minPt G) * Q := by nlinarith
      have h2 : G (reorderPt G lam K Q) ≤ G (minPt G) := le_of_mul_le_mul_right h1 hQ
      have h3 : reorderPt G lam K Q = minPt G := aux_hs_minPt_uniq hG (fun z => h2.trans (hs z))
      linarith
    · by_contra hcon
      push Not at hcon
      have hc := hG.conv _ _ (minPt G) (by linarith : reorderPt G lam K Q <
        reorderPt G lam K Q + Q) hcon
      rw [hfoc] at hc
      have h1 : G (reorderPt G lam K Q) * Q ≤ G (minPt G) * Q := by nlinarith
      have h2 : G (reorderPt G lam K Q) ≤ G (minPt G) := le_of_mul_le_mul_right h1 hQ
      have h3 : reorderPt G lam K Q + Q = minPt G :=
        aux_hs_minPt_uniq hG (fun z => by rw [hfoc]; exact h2.trans (hs z))
      linarith
  · subst hQ
    refine ⟨minPt G, minPt G, le_rfl, le_rfl, by ring, ?_, ?_⟩ <;>
    · unfold hFun; rw [if_neg (lt_irrefl 0)]

lemma aux_hs_cmp (hG : aux_hs_Good G h p m) {a b a' b' H H' : ℝ} (ha : a ≤ minPt G)
    (hb : minPt G ≤ b) (ha' : a' ≤ minPt G) (hb' : minPt G ≤ b')
    (hGa : G a = H) (hGb : G b = H) (hGa' : G a' = H') (hGb' : G b' = H') (hlt : H' < H) :
    a < a' ∧ b' < b ∧ (H - H') * (h + p) ≤ h * p * ((b - a) - (b' - a')) := by
  have hh := hG.hpos; have hp := hG.ppos
  have h1 : a < a' := by
    by_contra hc; push Not at hc
    have := aux_hs_anti hG hc ha
    linarith
  have h2 : b' < b := by
    by_contra hc; push Not at hc
    have := aux_hs_mono hG hb hc
    linarith
  refine ⟨h1, h2, ?_⟩
  have s1 := hG.sl a a' h1.le
  have s2 := hG.sr b' b h2.le
  rw [hGa, hGa'] at s1
  rw [hGb, hGb'] at s2
  nlinarith [mul_le_mul_of_nonneg_left s1 hh.le, mul_le_mul_of_nonneg_left s2 hp.le]

lemma aux_hs_Hmono (hG : aux_hs_Good G h p m) (lam K : ℝ) {Q Q' : ℝ} (hQ' : 0 ≤ Q')
    (hQQ : Q' ≤ Q) :
    hFun G lam K Q' ≤ hFun G lam K Q ∧
      (hFun G lam K Q - hFun G lam K Q') * (h + p) ≤ h * p * (Q - Q') := by
  have hh := hG.hpos; have hp := hG.ppos
  obtain ⟨a, b, ha, hb, hab, hGa, hGb⟩ := aux_hs_bracket hG lam K Q (hQ'.trans hQQ)
  obtain ⟨a', b', ha', hb', hab', hGa', hGb'⟩ := aux_hs_bracket hG lam K Q' hQ'
  rcases lt_or_ge (hFun G lam K Q') (hFun G lam K Q) with hlt | hle
  · have := aux_hs_cmp hG ha hb ha' hb' hGa hGb hGa' hGb' hlt
    refine ⟨hlt.le, ?_⟩
    rw [hab, hab'] at this; exact this.2.2
  · rcases hle.lt_or_eq with hlt | heq
    · have := aux_hs_cmp hG ha' hb' ha hb hGa' hGb' hGa hGb hlt
      exfalso; linarith [this.1, this.2.1]
    · rw [heq, sub_self, zero_mul]
      exact ⟨le_rfl, mul_nonneg (mul_nonneg hh.le hp.le) (by linarith)⟩

lemma aux_hs_Hlow (hG : aux_hs_Good G h p m) (lam K : ℝ) {Q : ℝ} (hQ : 0 ≤ Q) :
    h * p * Q ≤ hFun G lam K Q * (h + p) := by
  obtain ⟨a, b, ha, hb, hab, hGa, hGb⟩ := aux_hs_bracket hG lam K Q hQ
  have h1 := hG.lb2 a; have h2 := hG.lb1 b
  rw [hGa] at h1; rw [hGb] at h2
  have hh := hG.hpos; have hp := hG.ppos
  have e : h * p * Q = h * p * (b - a) := by rw [hab]
  nlinarith [mul_le_mul_of_nonneg_left h1 hh.le, mul_le_mul_of_nonneg_left h2 hp.le]

lemma aux_hs_H0 (G : ℝ → ℝ) (lam K : ℝ) : hFun G lam K 0 = G (minPt G) := by
  unfold hFun; rw [if_neg (lt_irrefl 0)]

end Abstract

end ZhengQR.EOQHeuristic

open ZhengQR.EOQHeuristic
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic
theorem ocb_hFun_sandwich {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) (Q : ℝ) (hQ : 0 ≤ Q) :
    h0Fun (newsvendorCost μ h p) lam K Q ≤ hFun (eoqCost lam L h p) lam K Q ∧
    hFun (eoqCost lam L h p) lam K Q ≤ hFun (newsvendorCost μ h p) lam K Q ∧
    aFun (newsvendorCost μ h p) lam K Q ≤ aFun (eoqCost lam L h p) lam K Q := by
  have hh := hM.h_pos
  have hp := hM.p_pos
  have hG := aux_hs_nv_good hM
  have hGd : aux_hs_Good (eoqCost lam L h p) h p (lam * L) := aux_hs_eoq_good hh hp
  have hhp : 0 < h + p := by linarith
  have hd0 : eoqCost lam L h p (minPt (eoqCost lam L h p)) = 0 := by
    have h1 := aux_hs_minPt_spec hGd (lam * L)
    have h2 := aux_hs_nonneg hGd (minPt (eoqCost lam L h p))
    have h3 : eoqCost lam L h p (lam * L) = 0 := by simp [eoqCost]
    linarith
  have hHd : ∀ y, 0 ≤ y → hFun (eoqCost lam L h p) lam K y = h * p / (h + p) * y := by
    intro y hy
    have h1 := (aux_hs_Hmono hGd lam K le_rfl hy).2
    have h2 := aux_hs_Hlow hGd lam K hy
    rw [aux_hs_H0, hd0, sub_zero, sub_zero] at h1
    rw [div_mul_eq_mul_div, eq_div_iff hhp.ne']
    linarith
  have hH0 := aux_hs_H0 (newsvendorCost μ h p) lam K
  refine ⟨?_, ?_, ?_⟩
  · unfold h0Fun
    have h1 := (aux_hs_Hmono hG lam K le_rfl hQ).2
    rw [hH0, sub_zero] at h1
    rw [hHd Q hQ, div_mul_eq_mul_div, le_div_iff₀ hhp]
    linarith
  · rw [hHd Q hQ, div_mul_eq_mul_div, div_le_iff₀ hhp]
    have := aux_hs_Hlow hG lam K hQ
    linarith
  · unfold aFun
    have hint_d : ∫ y in (0:ℝ)..Q, hFun (eoqCost lam L h p) lam K y =
        ∫ y in (0:ℝ)..Q, h * p / (h + p) * y := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [Set.uIcc_of_le hQ] at hy
      exact hHd y hy.1
    have hmonoOn : MonotoneOn (hFun (newsvendorCost μ h p) lam K) (Set.uIcc 0 Q) := by
      intro x hx y hy hxy
      rw [Set.uIcc_of_le hQ] at hx hy
      exact (aux_hs_Hmono hG lam K hx.1 hxy).1
    have hII := hmonoOn.intervalIntegrable (μ := volume)
    have hcont : Continuous (fun y : ℝ => hFun (newsvendorCost μ h p) lam K Q -
        h * p / (h + p) * (Q - y)) := by fun_prop
    have hlow : ∫ y in (0:ℝ)..Q, (hFun (newsvendorCost μ h p) lam K Q - h * p / (h + p) * (Q - y))
        ≤ ∫ y in (0:ℝ)..Q, hFun (newsvendorCost μ h p) lam K y := by
      apply intervalIntegral.integral_mono_on hQ (hcont.intervalIntegrable _ _) hII
      intro y hy
      have h1 := (aux_hs_Hmono hG lam K hy.1 hy.2).2
      have h2 : hFun (newsvendorCost μ h p) lam K Q - hFun (newsvendorCost μ h p) lam K y ≤
          h * p / (h + p) * (Q - y) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hhp]; linarith
      linarith
    have e1 : ∫ y in (0:ℝ)..Q, (hFun (newsvendorCost μ h p) lam K Q - h * p / (h + p) * (Q - y))
        = Q * hFun (newsvendorCost μ h p) lam K Q - h * p / (h + p) * (Q ^ 2 / 2) := by
      rw [intervalIntegral.integral_sub (intervalIntegrable_const (μ := volume))
        ((by fun_prop : Continuous (fun y : ℝ => h * p / (h + p) * (Q - y))).intervalIntegrable _ _),
        intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub (intervalIntegrable_const (μ := volume))
          intervalIntegral.intervalIntegrable_id, intervalIntegral.integral_const, integral_id]
      simp only [smul_eq_mul]
      ring
    have e2 : ∫ y in (0:ℝ)..Q, h * p / (h + p) * y = h * p / (h + p) * (Q ^ 2 / 2) := by
      rw [intervalIntegral.integral_const_mul, integral_id]; ring
    rw [hint_d, e2, hHd Q hQ]
    rw [e1] at hlow
    nlinarith

end ZhengQR.EOQHeuristic
end

section
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic

theorem aux_eoq_int {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (y : ℝ) :
    Integrable (fun x : ℝ => h * max (y - x) 0 + p * max (x - y) 0) μ := by
  have := hM.isProb
  exact (((integrable_const y).sub hM.integrable).pos_part.const_mul h).add
    ((hM.integrable.sub (integrable_const y)).pos_part.const_mul p)

theorem aux_eoq_up {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) {x y : ℝ}
    (hxy : x ≤ y) : newsvendorCost μ h p y ≤ newsvendorCost μ h p x + h * (y - x) := by
  have := hM.isProb
  unfold newsvendorCost
  have hmono : ∫ ω, (h * max (y - ω) 0 + p * max (ω - y) 0) ∂μ ≤
      ∫ ω, (h * max (x - ω) 0 + p * max (ω - x) 0 + h * (y - x)) ∂μ :=
    integral_mono (aux_eoq_int hM y) ((aux_eoq_int hM x).add (integrable_const (h * (y - x))))
    (fun ω => by
      have h1 : max (y - ω) 0 ≤ max (x - ω) 0 + (y - x) :=
        max_le (by linarith [le_max_left (x - ω) 0]) (by linarith [le_max_right (x - ω) 0])
      have h2 : max (ω - y) 0 ≤ max (ω - x) 0 := max_le_max (by linarith) le_rfl
      have := mul_le_mul_of_nonneg_left h1 hM.h_pos.le
      have := mul_le_mul_of_nonneg_left h2 hM.p_pos.le
      simp only [Pi.add_apply]
      nlinarith)
  rw [integral_add (aux_eoq_int hM x) (integrable_const _), integral_const] at hmono
  simpa using hmono

theorem aux_eoq_down {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) {x y : ℝ}
    (hxy : x ≤ y) : newsvendorCost μ h p x ≤ newsvendorCost μ h p y + p * (y - x) := by
  have := hM.isProb
  unfold newsvendorCost
  have hmono : ∫ ω, (h * max (x - ω) 0 + p * max (ω - x) 0) ∂μ ≤
      ∫ ω, (h * max (y - ω) 0 + p * max (ω - y) 0 + p * (y - x)) ∂μ :=
    integral_mono (aux_eoq_int hM x) ((aux_eoq_int hM y).add (integrable_const (p * (y - x))))
    (fun ω => by
      have h1 : max (ω - x) 0 ≤ max (ω - y) 0 + (y - x) :=
        max_le (by linarith [le_max_left (ω - y) 0]) (by linarith [le_max_right (ω - y) 0])
      have h2 : max (x - ω) 0 ≤ max (y - ω) 0 := max_le_max (by linarith) le_rfl
      have := mul_le_mul_of_nonneg_left h1 hM.p_pos.le
      have := mul_le_mul_of_nonneg_left h2 hM.h_pos.le
      simp only [Pi.add_apply]
      nlinarith)
  rw [integral_add (aux_eoq_int hM y) (integrable_const _), integral_const] at hmono
  simpa using hmono

theorem aux_eoq_low1 {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (y : ℝ) :
    h * (y - lam * L) ≤ newsvendorCost μ h p y := by
  have := hM.isProb
  unfold newsvendorCost
  have hmono : ∫ ω, h * (y - ω) ∂μ ≤ ∫ ω, (h * max (y - ω) 0 + p * max (ω - y) 0) ∂μ :=
    integral_mono (((integrable_const y).sub hM.integrable).const_mul h) (aux_eoq_int hM y)
    (fun ω => by
      have h1 : y - ω ≤ max (y - ω) 0 := le_max_left _ _
      have h2 : 0 ≤ max (ω - y) 0 := le_max_right _ _
      have := mul_le_mul_of_nonneg_left h1 hM.h_pos.le
      have := mul_nonneg hM.p_pos.le h2
      simp only [Pi.sub_apply]
      nlinarith)
  rw [integral_const_mul, integral_sub (integrable_const _) hM.integrable, integral_const, hM.mean] at hmono
  simpa using hmono

theorem aux_eoq_low2 {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (y : ℝ) :
    p * (lam * L - y) ≤ newsvendorCost μ h p y := by
  have := hM.isProb
  unfold newsvendorCost
  have hmono : ∫ ω, p * (ω - y) ∂μ ≤ ∫ ω, (h * max (y - ω) 0 + p * max (ω - y) 0) ∂μ :=
    integral_mono ((hM.integrable.sub (integrable_const y)).const_mul p) (aux_eoq_int hM y)
    (fun ω => by
      have h1 : ω - y ≤ max (ω - y) 0 := le_max_left _ _
      have h2 : 0 ≤ max (y - ω) 0 := le_max_right _ _
      have := mul_le_mul_of_nonneg_left h1 hM.p_pos.le
      have := mul_nonneg hM.h_pos.le h2
      simp only [Pi.sub_apply]
      nlinarith)
  rw [integral_const_mul, integral_sub hM.integrable (integrable_const _), integral_const, hM.mean] at hmono
  simpa using hmono

theorem aux_eoq_cont {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) :
    Continuous (newsvendorCost μ h p) := by
  have hL : ∀ x y, |newsvendorCost μ h p x - newsvendorCost μ h p y| ≤ (h + p) * |x - y| := by
    intro x y
    have hh := hM.h_pos
    have hp := hM.p_pos
    rcases le_total x y with hxy | hxy
    · have h1 := aux_eoq_up hM hxy
      have h2 := aux_eoq_down hM hxy
      rw [abs_of_nonpos (by linarith : x - y ≤ 0), abs_le]
      have := mul_nonneg hh.le (sub_nonneg.2 hxy)
      have := mul_nonneg hp.le (sub_nonneg.2 hxy)
      constructor <;> nlinarith
    · have h1 := aux_eoq_up hM hxy
      have h2 := aux_eoq_down hM hxy
      rw [abs_of_nonneg (by linarith : 0 ≤ x - y), abs_le]
      have := mul_nonneg hh.le (sub_nonneg.2 hxy)
      have := mul_nonneg hp.le (sub_nonneg.2 hxy)
      constructor <;> nlinarith
  have hLip : LipschitzWith (Real.toNNReal (h + p)) (newsvendorCost μ h p) :=
    LipschitzWith.of_dist_le_mul fun x y => by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by linarith [hM.h_pos, hM.p_pos])]
      exact hL x y
  exact hLip.continuous


theorem aux_eoq_winlow {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) {Q : ℝ}
    (hQ : 0 < Q) (r c : ℝ) (hc : ∀ y ∈ Set.Icc r (r + Q), c ≤ newsvendorCost μ h p y) :
    Q * c ≤ ∫ y in r..r + Q, newsvendorCost μ h p y := by
  have := intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
    ((aux_eoq_cont hM).intervalIntegrable (μ := volume) _ _) hc
  simpa using this

theorem aux_eoq_exists {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) {Q : ℝ}
    (hQ : 0 < Q) : ∃ r, ∀ r', ∫ y in r..r + Q, newsvendorCost μ h p y ≤
      ∫ y in r'..r' + Q, newsvendorCost μ h p y := by
  set G := newsvendorCost μ h p with hGdef
  have hG : Continuous G := aux_eoq_cont hM
  have hh := hM.h_pos
  have hp := hM.p_pos
  have hΦ : Continuous (fun x => ∫ y in (0:ℝ)..x, G y) :=
    intervalIntegral.continuous_primitive (μ := volume) (fun a b => hG.intervalIntegrable a b) 0
  have hφ : Continuous (fun r => ∫ y in r..r + Q, G y) := by
    have : (fun r => ∫ y in r..r + Q, G y) =
        fun r => (∫ y in (0:ℝ)..(r + Q), G y) - ∫ y in (0:ℝ)..r, G y := by
      funext r
      rw [intervalIntegral.integral_interval_sub_left (hG.intervalIntegrable _ _)
        (hG.intervalIntegrable _ _)]
    rw [this]
    exact (hΦ.comp (continuous_id.add continuous_const)).sub hΦ
  set m := lam * L
  set φ0 := ∫ y in (0:ℝ)..0 + Q, G y
  refine hφ.exists_forall_le' 0 ?_
  rw [cocompact_eq_atBot_atTop, Filter.eventually_sup]
  constructor
  · rw [Filter.eventually_atBot]
    refine ⟨m - Q - φ0 / (Q * p), fun r hr => ?_⟩
    have hlow := aux_eoq_winlow hM hQ r (p * (m - r - Q)) (fun y hy => by
      have := aux_eoq_low2 hM y
      have : p * (m - r - Q) ≤ p * (m - y) :=
        mul_le_mul_of_nonneg_left (by linarith [hy.2]) hp.le
      linarith)
    have h1 : φ0 / (Q * p) ≤ m - r - Q := by linarith
    rw [div_le_iff₀ (by positivity)] at h1
    show φ0 ≤ _
    nlinarith
  · rw [Filter.eventually_atTop]
    refine ⟨m + φ0 / (Q * h), fun r hr => ?_⟩
    have hlow := aux_eoq_winlow hM hQ r (h * (r - m)) (fun y hy => by
      have := aux_eoq_low1 hM y
      have : h * (r - m) ≤ h * (y - m) :=
        mul_le_mul_of_nonneg_left (by linarith [hy.1]) hh.le
      linarith)
    have h1 : φ0 / (Q * h) ≤ r - m := by linarith
    rw [div_le_iff₀ (by positivity)] at h1
    show φ0 ≤ _
    nlinarith

theorem aux_eoq_reorder {lam L h p K : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) {Q : ℝ}
    (hQ : 0 < Q) (r' : ℝ) :
    optCost (newsvendorCost μ h p) lam K Q ≤ qrCost (newsvendorCost μ h p) lam K Q r' := by
  obtain ⟨r, hr⟩ := aux_eoq_exists hM hQ
  have hex : ∃ r, IsOptReorder (newsvendorCost μ h p) lam K Q r := ⟨r, fun r'' => by
    unfold qrCost
    exact div_le_div_of_nonneg_right (by linarith [hr r'']) hQ.le⟩
  unfold optCost reorderPt
  rw [dif_pos hex]
  exact hex.choose_spec r'

theorem aux_eoq_affine1 (α p r s : ℝ) :
    ∫ y in r..r + s, (α - p * (y - r)) = α * s - p * s ^ 2 / 2 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y => α * y - p * (y - r) ^ 2 / 2)]
  · ring
  · intro x _
    have h1 : HasDerivAt (fun y => α * y - p * (y - r) ^ 2 / 2)
        (α * 1 - p * ((2:ℕ) * (x - r) ^ (2 - 1) * 1) / 2) x :=
      ((hasDerivAt_id' x).const_mul α).sub
        ((((hasDerivAt_id' x).sub_const r).pow 2).const_mul p |>.div_const 2)
    exact h1.congr_deriv (by norm_num <;> ring)
  · exact (continuous_const.sub (continuous_const.mul (continuous_id.sub continuous_const))).intervalIntegrable _ _

theorem aux_eoq_affine2 (β h b u : ℝ) :
    ∫ y in b - u..b, (β - h * (b - y)) = β * u - h * u ^ 2 / 2 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun y => β * y + h * (b - y) ^ 2 / 2)]
  · ring
  · intro x _
    have h1 : HasDerivAt (fun y => β * y + h * (b - y) ^ 2 / 2)
        (β * 1 + h * ((2:ℕ) * (b - x) ^ (2 - 1) * (-1)) / 2) x :=
      ((hasDerivAt_id' x).const_mul β).add
        ((((hasDerivAt_id' x).const_sub b).pow 2).const_mul h |>.div_const 2)
    exact h1.congr_deriv (by norm_num <;> ring)
  · exact (continuous_const.sub (continuous_const.mul (continuous_const.sub continuous_id))).intervalIntegrable _ _


end ZhengQR.EOQHeuristic

open ZhengQR.EOQHeuristic

namespace ZhengQR.EOQHeuristic
theorem ocb_eoqQty_le_optQty {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) (Qs : ℝ)
    (hQs : IsOptQty (newsvendorCost μ h p) lam K Qs) :
    eoqQty lam K h p ≤ Qs := by
  obtain ⟨hQ, hopt⟩ := hQs
  have hh := hM.h_pos
  have hp := hM.p_pos
  set G := newsvendorCost μ h p with hGdef
  have hG : Continuous G := aux_eoq_cont hM
  set r := reorderPt G lam K Qs with hr
  set I := ∫ y in r..r + Qs, G y with hI
  have keyR : ∀ Δ > 0, lam * K + I ≤ Qs * G (r + Qs) + Qs * h * Δ := by
    intro Δ hΔ
    have h1 := hopt (Qs + Δ) (by positivity)
    have h2 := aux_eoq_reorder (K := K) hM (Q := Qs + Δ) (by positivity) r
    have h3 : ∫ y in r..r + (Qs + Δ), G y ≤ I + Δ * (G (r + Qs) + h * Δ) := by
      rw [← add_assoc, ← intervalIntegral.integral_add_adjacent_intervals (b := r + Qs)
        (hG.intervalIntegrable _ _) (hG.intervalIntegrable _ _)]
      have h4 := intervalIntegral.integral_mono_on (μ := volume) (a := r + Qs) (b := r + Qs + Δ) (f := G)
        (g := fun _ => G (r + Qs) + h * Δ) (by linarith) (hG.intervalIntegrable _ _)
        intervalIntegrable_const (fun y hy => by
          have := aux_eoq_up hM hy.1
          have : h * (y - (r + Qs)) ≤ h * Δ :=
            mul_le_mul_of_nonneg_left (by linarith [hy.2]) hh.le
          linarith)
      simp at h4
      linarith
    have h5 : (lam * K + I) / Qs ≤ (lam * K + I + Δ * (G (r + Qs) + h * Δ)) / (Qs + Δ) := by
      calc (lam * K + I) / Qs = optCost G lam K Qs := rfl
        _ ≤ optCost G lam K (Qs + Δ) := h1
        _ ≤ qrCost G lam K (Qs + Δ) r := h2
        _ ≤ _ := by
          unfold qrCost
          exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    rw [div_le_div_iff₀ hQ (by positivity)] at h5
    have h6 : Δ * (lam * K + I) ≤ Δ * (Qs * G (r + Qs) + Qs * h * Δ) := by nlinarith
    exact le_of_mul_le_mul_left h6 hΔ
  have keyL : ∀ Δ > 0, lam * K + I ≤ Qs * G r + Qs * p * Δ := by
    intro Δ hΔ
    have h1 := hopt (Qs + Δ) (by positivity)
    have h2 := aux_eoq_reorder (K := K) hM (Q := Qs + Δ) (by positivity) (r - Δ)
    have h3 : ∫ y in (r - Δ)..(r - Δ) + (Qs + Δ), G y ≤ I + Δ * (G r + p * Δ) := by
      rw [show r - Δ + (Qs + Δ) = r + Qs by ring,
        ← intervalIntegral.integral_add_adjacent_intervals (b := r)
        (hG.intervalIntegrable _ _) (hG.intervalIntegrable _ _)]
      have h4 := intervalIntegral.integral_mono_on (μ := volume) (a := r - Δ) (b := r) (f := G)
        (g := fun _ => G r + p * Δ) (by linarith) (hG.intervalIntegrable _ _)
        intervalIntegrable_const (fun y hy => by
          have := aux_eoq_down hM hy.2
          have : p * (r - y) ≤ p * Δ :=
            mul_le_mul_of_nonneg_left (by linarith [hy.1]) hp.le
          linarith)
      simp at h4
      linarith
    have h5 : (lam * K + I) / Qs ≤ (lam * K + I + Δ * (G r + p * Δ)) / (Qs + Δ) := by
      calc (lam * K + I) / Qs = optCost G lam K Qs := rfl
        _ ≤ optCost G lam K (Qs + Δ) := h1
        _ ≤ qrCost G lam K (Qs + Δ) (r - Δ) := h2
        _ ≤ _ := by
          unfold qrCost
          exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    rw [div_le_div_iff₀ hQ (by positivity)] at h5
    have h6 : Δ * (lam * K + I) ≤ Δ * (Qs * G r + Qs * p * Δ) := by nlinarith
    exact le_of_mul_le_mul_left h6 hΔ
  have hα : lam * K + I ≤ Qs * G r := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have := keyL (ε / (Qs * p)) (by positivity)
    have e : Qs * p * (ε / (Qs * p)) = ε := by field_simp
    linarith
  have hβ : lam * K + I ≤ Qs * G (r + Qs) := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have := keyR (ε / (Qs * h)) (by positivity)
    have e : Qs * h * (ε / (Qs * h)) = ε := by field_simp
    linarith
  set s := h * Qs / (h + p) with hs
  set u := p * Qs / (h + p) with hu
  have hs' : s * (h + p) = h * Qs := by rw [hs]; field_simp
  have hu' : u * (h + p) = p * Qs := by rw [hu]; field_simp
  have hsu : s + u = Qs := by rw [hs, hu]; field_simp
  have hs0 : 0 ≤ s := by positivity
  have hu0 : 0 ≤ u := by positivity
  have hI1 : G r * s - p * s ^ 2 / 2 ≤ ∫ y in r..r + s, G y := by
    rw [← aux_eoq_affine1 (G r) p r s]
    exact intervalIntegral.integral_mono_on (by linarith)
      ((continuous_const.sub (continuous_const.mul (continuous_id.sub continuous_const))).intervalIntegrable _ _)
      (hG.intervalIntegrable _ _) (fun y hy => by have := aux_eoq_down hM hy.1; linarith)
  have hI2 : G (r + Qs) * u - h * u ^ 2 / 2 ≤ ∫ y in (r + Qs) - u..r + Qs, G y := by
    rw [← aux_eoq_affine2 (G (r + Qs)) h (r + Qs) u]
    exact intervalIntegral.integral_mono_on (by linarith)
      ((continuous_const.sub (continuous_const.mul (continuous_const.sub continuous_id))).intervalIntegrable _ _)
      (hG.intervalIntegrable _ _) (fun y hy => by have := aux_eoq_up hM hy.2; linarith)
  have hsplit : I = (∫ y in r..r + s, G y) + ∫ y in (r + Qs) - u..r + Qs, G y := by
    have : r + Qs - u = r + s := by linarith
    rw [this, intervalIntegral.integral_add_adjacent_intervals (hG.intervalIntegrable _ _)
      (hG.intervalIntegrable _ _)]
  have hfin : (h + p) * (lam * K) ≤ h * p * Qs ^ 2 / 2 := by
    have e1 := mul_le_mul_of_nonneg_left hα hh.le
    have e2 := mul_le_mul_of_nonneg_left hβ hp.le
    have e3 : (h + p) * (G r * s + G (r + Qs) * u) = Qs * (h * G r + p * G (r + Qs)) := by
      linear_combination G r * hs' + G (r + Qs) * hu'
    have e4 : (h + p) * (p * s ^ 2 + h * u ^ 2) = h * p * Qs ^ 2 := by
      linear_combination p * s * hs' + h * u * hu' + h * p * Qs * hsu
    have e5 : (h + p) * (G r * s - p * s ^ 2 / 2 + (G (r + Qs) * u - h * u ^ 2 / 2)) ≤
        (h + p) * I := by
      rw [hsplit]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    nlinarith
  unfold eoqQty
  rw [Real.sqrt_le_left hQ.le, div_le_iff₀ (by positivity)]
  nlinarith

end ZhengQR.EOQHeuristic
end

namespace ZhengQR.CostBounds

open MeasureTheory

theorem ocb_core (M : QRModel) (Qs : ℝ) (hQs : IsOptQty M.G M.lam M.K Qs) :
    C0fun M.G M.lam M.K Qs ≤ M.Qd / Qs * Cfun M.Gd M.lam M.K M.Qd ∧
    Cfun M.Gd M.lam M.K M.Qd ≤ Cfun M.G M.lam M.K Qs ∧
    Cfun M.G M.lam M.K Qs ≤ M.G (idealPt M.G) + M.Qd / Qs * Cfun M.Gd M.lam M.K M.Qd := by
  have hlam := M.lam_pos
  have hK := M.K_pos
  have hh := M.h_pos
  have hp := M.p_pos
  have hQ0 : 0 < Qs := hQs.1
  have hM : EOQHeuristic.IsQRModel M.lam M.L M.h M.p M.μ :=
    ⟨M.lam_pos, M.L_pos, M.h_pos, M.p_pos, M.isProb, M.integrable_id, M.mean_eq,
      M.demand_nonneg, M.unique_min⟩
  have hQs' : EOQHeuristic.IsOptQty (EOQHeuristic.newsvendorCost M.μ M.h M.p) M.lam M.K Qs := hQs
  have hQd : M.Qd ≤ Qs := EOQHeuristic.ocb_eoqQty_le_optQty hM hK Qs hQs'
  have hprops := EOQHeuristic.ocb_hFun_props hM hK
  have hconv : ConvexOn ℝ (Set.Ici 0) (Hfun M.G M.lam M.K) := hprops.2.1
  have hsand := EOQHeuristic.ocb_hFun_sandwich hM hK Qs hQ0.le
  have hsand2 : Hfun M.Gd M.lam M.K Qs ≤ Hfun M.G M.lam M.K Qs := hsand.2.1
  obtain ⟨hdec1, hdec2⟩ := ocb_cost_decomposition M
  obtain ⟨hHd, -, hCd⟩ := ocb_eoq_optimum M
  have hHdQs : Hfun M.Gd M.lam M.K Qs = M.h * M.p / (M.h + M.p) * Qs := hHd Qs hQ0.le
  have hQdnn : 0 ≤ M.Qd := Real.sqrt_nonneg _
  have hCdQd : Cfun M.Gd M.lam M.K M.Qd = M.h * M.p / (M.h + M.p) * M.Qd := by
    rw [hCd, hHd _ hQdnn]
  have hQd2 : M.Qd ^ 2 = 2 * M.lam * M.K * (M.h + M.p) / (M.h * M.p) :=
    Real.sq_sqrt (by positivity)
  have hC0 : C0fun M.G M.lam M.K Qs = H0fun M.G M.lam M.K Qs := (hdec2 Qs hQs).symm
  have hC : Cfun M.G M.lam M.K Qs = Hfun M.G M.lam M.K Qs := by
    rw [hdec1 Qs hQ0, hC0]; unfold H0fun; ring
  -- integral bound
  have hHc : Continuous (Hfun M.G M.lam M.K) := aux_cd_H_cont (aux_cd_good M) M.lam M.K
  have hH0c : Continuous (H0fun M.G M.lam M.K) := by
    unfold H0fun; exact hHc.sub continuous_const
  have hH00 : H0fun M.G M.lam M.K 0 = 0 := by
    unfold H0fun Hfun; simp
  have hpt : ∀ y ∈ Set.Icc (0 : ℝ) Qs,
      H0fun M.G M.lam M.K y ≤ y * (H0fun M.G M.lam M.K Qs / Qs) := by
    intro y hy
    have ha : 0 ≤ 1 - y / Qs := by
      rw [sub_nonneg, div_le_one hQ0]; exact hy.2
    have hb : 0 ≤ y / Qs := div_nonneg hy.1 hQ0.le
    have := hconv.2 (show (0:ℝ) ∈ Set.Ici (0:ℝ) from Set.self_mem_Ici) (show Qs ∈ Set.Ici (0:ℝ) from hQ0.le) ha hb (by ring)
    have e : (1 - y / Qs) • (0:ℝ) + (y / Qs) • Qs = y := by
      simp [smul_eq_mul]; field_simp
    rw [e] at this
    simp only [smul_eq_mul] at this
    have e0 : Hfun M.G M.lam M.K 0 = M.G (idealPt M.G) := by unfold Hfun; simp
    unfold H0fun
    rw [e0] at this
    have e2 : y * ((Hfun M.G M.lam M.K Qs - M.G (idealPt M.G)) / Qs)
        = y / Qs * (Hfun M.G M.lam M.K Qs - M.G (idealPt M.G)) := by ring
    rw [e2]; nlinarith
  have hint : ∫ y in (0:ℝ)..Qs, H0fun M.G M.lam M.K y ≤ 1 / 2 * Qs * H0fun M.G M.lam M.K Qs := by
    have := intervalIntegral.integral_mono_on hQ0.le (hH0c.intervalIntegrable (μ := volume) _ _)
      ((show Continuous (fun y : ℝ => y * (H0fun M.G M.lam M.K Qs / Qs)) by fun_prop).intervalIntegrable (μ := volume) _ _) hpt
    rw [intervalIntegral.integral_mul_const, integral_id] at this
    have e : (Qs ^ 2 - 0 ^ 2) / 2 * (H0fun M.G M.lam M.K Qs / Qs)
        = 1 / 2 * Qs * H0fun M.G M.lam M.K Qs := by field_simp; ring
    linarith
  have hC0def : C0fun M.G M.lam M.K Qs * Qs
      = M.lam * M.K + ∫ y in (0:ℝ)..Qs, H0fun M.G M.lam M.K y := by
    unfold C0fun; field_simp
  have hkey : C0fun M.G M.lam M.K Qs * Qs ≤ 2 * (M.lam * M.K) := by
    rw [← hC0] at hint; nlinarith
  have hR : M.Qd / Qs * Cfun M.Gd M.lam M.K M.Qd = 2 * (M.lam * M.K) / Qs := by
    rw [hCdQd]
    have e : M.Qd / Qs * (M.h * M.p / (M.h + M.p) * M.Qd)
        = M.h * M.p / (M.h + M.p) * M.Qd ^ 2 / Qs := by ring
    rw [e, hQd2]
    field_simp
  have hpart1 : C0fun M.G M.lam M.K Qs ≤ M.Qd / Qs * Cfun M.Gd M.lam M.K M.Qd := by
    rw [hR, le_div_iff₀ hQ0]; exact hkey
  refine ⟨hpart1, ?_, ?_⟩
  · rw [hCdQd, hC]
    have hc : 0 ≤ M.h * M.p / (M.h + M.p) := by positivity
    have := mul_le_mul_of_nonneg_left hQd hc
    linarith
  · rw [hdec1 Qs hQ0]; linarith

end ZhengQR.CostBounds

open ZhengQR.CostBounds


theorem solution (M : QRModel) (Qs : ℝ) (hQs : IsOptQty M.G M.lam M.K Qs) :
    C0fun M.G M.lam M.K Qs ≤ M.Qd / Qs * Cfun M.Gd M.lam M.K M.Qd ∧
    Cfun M.Gd M.lam M.K M.Qd ≤ Cfun M.G M.lam M.K Qs ∧
    Cfun M.G M.lam M.K Qs ≤ M.G (idealPt M.G) + M.Qd / Qs * Cfun M.Gd M.lam M.K M.Qd := by
  exact ocb_core M Qs hQs
