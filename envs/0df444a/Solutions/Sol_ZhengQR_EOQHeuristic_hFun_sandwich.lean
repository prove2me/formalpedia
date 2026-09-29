-- Prove2me | solution 1 for ZhengQR.EOQHeuristic.hFun_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:36:38.816954+00:00
-- url     : https://prove2.me/submissions/e0634ef1-5854-40f9-b0bd-012b82e0456e

import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_costCurves
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
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

theorem solution {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) (Q : ℝ) (hQ : 0 ≤ Q) :
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
