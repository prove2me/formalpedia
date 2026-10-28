-- Prove2me | solution 2 for ZhengQR.CostBounds.optimal_cost_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T07:31:14.851965+00:00
-- url     : https://prove2.me/submissions/cf208349-9fb4-4d17-9ad1-5c154bff6af1

import Mathlib
import Definitions.Def_ZhengQR_CostBounds_QRMachinery
import Definitions.Def_ZhengQR_CostBounds_Model
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_costCurves
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
import Theorems.Thm_ZhengQR_EOQHeuristic_eoqQty_le_optQty
import Theorems.Thm_ZhengQR_CostBounds_eoq_optimum
import Theorems.Thm_ZhengQR_EOQHeuristic_hFun_props

-- carved verbatim out of submission 9c5eb7b1-2620-42d7-9760-b9ad4161c330, lines 2049-2054

section
open ZhengQR
open ZhengQR.CostBounds
open MeasureTheory Filter Topology

structure aux_cd_Good (G : ℝ → ℝ) : Prop where
  lip : ∃ L : ℝ, 0 < L ∧ ∀ y y' : ℝ, |G y - G y'| ≤ L * |y - y'|
  conv : ∀ x z a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → G (a * x + b * z) ≤ a * G x + b * G z
  coer : ∃ c1 c2 m : ℝ, 0 < c1 ∧ 0 < c2 ∧ ∀ y : ℝ, c1 * (y - m) ≤ G y ∧ c2 * (m - y) ≤ G y
  umin : ∃! y : ℝ, ∀ z : ℝ, G y ≤ G z

end

section
open ZhengQR
open ZhengQR.CostBounds
open MeasureTheory Filter Topology
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

end

section
open ZhengQR
open ZhengQR.CostBounds
open MeasureTheory Filter Topology
variable {G : ℝ → ℝ}

noncomputable def aux_cd_Phi (G : ℝ → ℝ) (u : ℝ) : ℝ := ∫ y in (0 : ℝ)..u, G y

noncomputable def aux_cd_rho (G : ℝ → ℝ) (lam K t : ℝ) : ℝ :=
  if 0 < t then reorderPt G lam K t else idealPt G

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

end

section
open ZhengQR
open ZhengQR.CostBounds
open MeasureTheory Filter Topology

lemma aux_cd_good (M : QRModel) : aux_cd_Good M.G := by
  have := M.isProb
  exact ⟨⟨M.h + M.p, by linarith [M.h_pos, M.p_pos],
      aux_cd_lip M.integrable_id M.h_pos M.p_pos⟩,
    aux_cd_conv M.integrable_id M.h_pos M.p_pos,
    ⟨M.h, M.p, ∫ x, x ∂M.μ, M.h_pos, M.p_pos, aux_cd_coer M.integrable_id M.h_pos M.p_pos⟩,
    M.unique_min⟩

end

section
open ZhengQR.CostBounds
open ZhengQR

theorem ocb_cost_decomposition (M : QRModel) :
    (∀ Q : ℝ, 0 < Q →
      Cfun M.G M.lam M.K Q = M.G (idealPt M.G) + C0fun M.G M.lam M.K Q) ∧
    (∀ Qs : ℝ, IsOptQty M.G M.lam M.K Qs →
      H0fun M.G M.lam M.K Qs = C0fun M.G M.lam M.K Qs) :=
  ⟨fun _ hQ => aux_cd_part1 (aux_cd_good M) M.lam M.K hQ,
   fun _ h => aux_cd_part2 (aux_cd_good M) M.lam M.K h⟩

end

section
open MeasureTheory Filter Topology
open ZhengQR
open ZhengQR.EOQHeuristic

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

end

section
open MeasureTheory Filter Topology
open ZhengQR
open ZhengQR.EOQHeuristic
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

end

section
open MeasureTheory Filter Topology
open ZhengQR.EOQHeuristic
open ZhengQR

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

end

section
open ZhengQR
open ZhengQR.CostBounds
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
  have hQd : M.Qd ≤ Qs := ZhengQR.EOQHeuristic.eoqQty_le_optQty hM hK Qs hQs'
  have hprops := ZhengQR.EOQHeuristic.hFun_props hM hK
  have hconv : ConvexOn ℝ (Set.Ici 0) (Hfun M.G M.lam M.K) := hprops.2.1
  have hsand := ocb_hFun_sandwich hM hK Qs hQ0.le
  have hsand2 : Hfun M.Gd M.lam M.K Qs ≤ Hfun M.G M.lam M.K Qs := hsand.2.1
  obtain ⟨hdec1, hdec2⟩ := ocb_cost_decomposition M
  obtain ⟨hHd, -, hCd⟩ := ZhengQR.CostBounds.eoq_optimum M
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

end

section
open ZhengQR.CostBounds

theorem solution (M : QRModel) (Qs : ℝ) (hQs : IsOptQty M.G M.lam M.K Qs) :
    C0fun M.G M.lam M.K Qs ≤ M.Qd / Qs * Cfun M.Gd M.lam M.K M.Qd ∧
    Cfun M.Gd M.lam M.K M.Qd ≤ Cfun M.G M.lam M.K Qs ∧
    Cfun M.G M.lam M.K Qs ≤ M.G (idealPt M.G) + M.Qd / Qs * Cfun M.Gd M.lam M.K M.Qd := by
  exact ocb_core M Qs hQs

end
