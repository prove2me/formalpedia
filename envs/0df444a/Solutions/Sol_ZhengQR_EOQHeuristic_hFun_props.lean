-- Prove2me | solution 1 for ZhengQR.EOQHeuristic.hFun_props
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:27:50.409985+00:00
-- url     : https://prove2.me/submissions/e55ce46b-31a4-41e0-b0a0-a799cddd38d9

import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_costCurves
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
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

theorem solution {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) :
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
