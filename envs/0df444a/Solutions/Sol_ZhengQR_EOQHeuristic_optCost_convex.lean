-- Prove2me | solution 1 for ZhengQR.EOQHeuristic.optCost_convex
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T01:43:46.596171+00:00
-- url     : https://prove2.me/submissions/3e94252e-2a61-4204-b580-a58fa57289b9

import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_costCurves
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic

lemma aux_oc_integrable {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hint : Integrable (fun x : ℝ => x) μ) (h p y : ℝ) :
    Integrable (fun x => h * max (y - x) 0 + p * max (x - y) 0) μ := by
  have h1 : Integrable (fun x : ℝ => y - x) μ := (integrable_const y).sub hint
  have h2 : Integrable (fun x : ℝ => x - y) μ := hint.sub (integrable_const y)
  exact (h1.pos_part.const_mul h).add (h2.pos_part.const_mul p)

lemma aux_oc_convex {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) :
    ConvexOn ℝ Set.univ (newsvendorCost μ h p) := by
  have := hM.isProb
  refine ⟨convex_univ, fun y1 _ y2 _ a b ha hb hab => ?_⟩
  simp only [newsvendorCost, smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add]
  · apply integral_mono (aux_oc_integrable hM.integrable h p _)
    · exact ((aux_oc_integrable hM.integrable h p y1).const_mul a).add
        ((aux_oc_integrable hM.integrable h p y2).const_mul b)
    · intro x
      have key : ∀ u v : ℝ, max (a*u+b*v) 0 ≤ a * max u 0 + b * max v 0 := by
        intro u v
        apply max_le
        · have := mul_le_mul_of_nonneg_left (le_max_left u 0) ha
          have := mul_le_mul_of_nonneg_left (le_max_left v 0) hb
          linarith
        · have := mul_nonneg ha (le_max_right u 0)
          have := mul_nonneg hb (le_max_right v 0)
          linarith
      have hx : a * x + b * x = x := by rw [← add_mul, hab, one_mul]
      have e1 : a * y1 + b * y2 - x = a * (y1 - x) + b * (y2 - x) := by linarith
      have e2 : x - (a * y1 + b * y2) = a * (x - y1) + b * (x - y2) := by linarith
      simp only
      rw [e1, e2]
      have k1 := mul_le_mul_of_nonneg_left (key (y1 - x) (y2 - x)) hM.h_pos.le
      have k2 := mul_le_mul_of_nonneg_left (key (x - y1) (x - y2)) hM.p_pos.le
      linarith
  · exact (aux_oc_integrable hM.integrable h p y1).const_mul a
  · exact (aux_oc_integrable hM.integrable h p y2).const_mul b

lemma aux_oc_cont {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) :
    Continuous (newsvendorCost μ h p) :=
  continuousOn_univ.mp ((aux_oc_convex hM).continuousOn isOpen_univ)

lemma aux_oc_lb1 {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (y : ℝ) :
    h * (y - lam * L) ≤ newsvendorCost μ h p y := by
  have := hM.isProb
  have hi : Integrable (fun x : ℝ => h * (y - x)) μ :=
    ((integrable_const y).sub hM.integrable).const_mul h
  have : ∫ x, h * (y - x) ∂μ = h * (y - lam * L) := by
    rw [integral_const_mul, integral_sub (integrable_const y) hM.integrable, hM.mean]
    simp
  rw [← this]
  apply integral_mono hi (aux_oc_integrable hM.integrable h p y)
  intro x
  simp only
  have k1 := mul_le_mul_of_nonneg_left (le_max_left (y - x) 0) hM.h_pos.le
  have k2 := mul_nonneg hM.p_pos.le (le_max_right (x - y) 0)
  linarith

lemma aux_oc_lb2 {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (y : ℝ) :
    p * (lam * L - y) ≤ newsvendorCost μ h p y := by
  have := hM.isProb
  have hi : Integrable (fun x : ℝ => p * (x - y)) μ :=
    (hM.integrable.sub (integrable_const y)).const_mul p
  have : ∫ x, p * (x - y) ∂μ = p * (lam * L - y) := by
    rw [integral_const_mul, integral_sub hM.integrable (integrable_const y), hM.mean]
    simp
  rw [← this]
  apply integral_mono hi (aux_oc_integrable hM.integrable h p y)
  intro x
  simp only
  have k1 := mul_le_mul_of_nonneg_left (le_max_left (x - y) 0) hM.p_pos.le
  have k2 := mul_nonneg hM.h_pos.le (le_max_right (y - x) 0)
  linarith

lemma aux_oc_exists {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ)
    {Q : ℝ} (hQ : 0 < Q) :
    ∃ r, IsOptReorder (newsvendorCost μ h p) lam K Q r := by
  set G := newsvendorCost μ h p with hG
  have hGc : Continuous G := aux_oc_cont hM
  have hii : ∀ a b, IntervalIntegrable G volume a b := fun a b => hGc.intervalIntegrable a b
  set φ : ℝ → ℝ := fun r => ∫ y in r..r + Q, G y with hφ
  have hφc : Continuous φ := by
    have : φ = fun r => (∫ y in (0:ℝ)..r + Q, G y) - ∫ y in (0:ℝ)..r, G y := by
      funext r
      simp only [hφ]
      rw [intervalIntegral.integral_interval_sub_left (hii _ _) (hii _ _)]
    rw [this]
    exact ((intervalIntegral.continuous_primitive hii 0).comp (continuous_add_const Q)).sub
      (intervalIntegral.continuous_primitive hii 0)
  have hlow1 : ∀ r, Q * (h * (r - lam * L)) ≤ φ r := by
    intro r
    have := intervalIntegral.integral_mono_on (by linarith : r ≤ r + Q)
      (intervalIntegrable_const) (hii r (r+Q))
      (fun y hy => (show h * (r - lam*L) ≤ G y from
        le_trans (by nlinarith [hy.1, hM.h_pos]) (aux_oc_lb1 hM y)))
    simp only [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] at this
    exact this
  have hlow2 : ∀ r, Q * (p * (lam * L - (r + Q))) ≤ φ r := by
    intro r
    have := intervalIntegral.integral_mono_on (by linarith : r ≤ r + Q)
      (intervalIntegrable_const) (hii r (r+Q))
      (fun y hy => (show p * (lam * L - (r + Q)) ≤ G y from
        le_trans (by nlinarith [hy.2, hM.p_pos]) (aux_oc_lb2 hM y)))
    simp only [intervalIntegral.integral_const, smul_eq_mul, add_sub_cancel_left] at this
    exact this
  have hQh : 0 < Q * h := mul_pos hQ hM.h_pos
  have hQp : 0 < Q * p := mul_pos hQ hM.p_pos
  have hlim : Tendsto φ (cocompact ℝ) atTop := by
    rw [cocompact_eq_atBot_atTop]
    refine tendsto_sup.2 ⟨?_, ?_⟩
    · refine tendsto_atTop_mono (fun r => ?_)
        (tendsto_atTop_add_const_right _ (Q * p * (lam * L - Q))
          (tendsto_neg_atBot_atTop.const_mul_atTop hQp))
      have := hlow2 r
      linarith
    · refine tendsto_atTop_mono (fun r => ?_)
        (tendsto_atTop_add_const_right _ (-(Q * h * (lam * L)))
          (tendsto_id.const_mul_atTop hQh))
      have := hlow1 r
      simp only [id]
      linarith
  obtain ⟨r0, hr0⟩ := hφc.exists_forall_le hlim
  refine ⟨r0, fun r' => ?_⟩
  unfold qrCost
  have := hr0 r'
  simp only [hφ] at this
  gcongr

lemma aux_oc_repr (G : ℝ → ℝ) (lam K : ℝ) {Q : ℝ} (hQ : 0 < Q) (r : ℝ) :
    qrCost G lam K Q r = lam * K / Q + ∫ t in (0:ℝ)..1, G (Q * t + r) := by
  rw [intervalIntegral.integral_comp_mul_add G hQ.ne' r]
  simp only [mul_zero, zero_add, mul_one, smul_eq_mul, qrCost]
  rw [add_comm Q r]
  field_simp

end ZhengQR.EOQHeuristic

open ZhengQR.EOQHeuristic

theorem solution {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) :
    ConvexOn ℝ (Set.Ioi 0) (optCost (newsvendorCost μ h p) lam K) := by
  set G := newsvendorCost μ h p with hG
  have hGcv : ConvexOn ℝ Set.univ G := aux_oc_convex hM
  have hGc : Continuous G := aux_oc_cont hM
  refine ⟨convex_Ioi 0, fun Q1 hQ1 Q2 hQ2 a b ha hb hab => ?_⟩
  have hQ : a • Q1 + b • Q2 ∈ Set.Ioi (0:ℝ) := convex_Ioi 0 hQ1 hQ2 ha hb hab
  have hinv := (convexOn_zpow (𝕜 := ℝ) (-1)).2 hQ1 hQ2 ha hb hab
  simp only [smul_eq_mul, Set.mem_Ioi] at hQ hQ1 hQ2 hinv ⊢
  simp only [zpow_neg, zpow_one] at hinv
  set r1 := reorderPt G lam K Q1
  set r2 := reorderPt G lam K Q2
  have hopt : IsOptReorder G lam K (a*Q1+b*Q2) (reorderPt G lam K (a*Q1+b*Q2)) := by
    have hex := aux_oc_exists (K := K) hM hQ
    unfold reorderPt
    rw [dif_pos hex]
    exact hex.choose_spec
  have hc : 0 ≤ lam * K := (mul_pos hM.lam_pos hK).le
  calc optCost G lam K (a*Q1+b*Q2) ≤ qrCost G lam K (a*Q1+b*Q2) (a*r1+b*r2) := hopt _
    _ ≤ a * qrCost G lam K Q1 r1 + b * qrCost G lam K Q2 r2 := by
        rw [aux_oc_repr G lam K hQ, aux_oc_repr G lam K hQ1, aux_oc_repr G lam K hQ2]
        have h1 : lam * K / (a*Q1+b*Q2) ≤ a * (lam*K/Q1) + b * (lam*K/Q2) := by
          have := mul_le_mul_of_nonneg_left hinv hc
          simp only [div_eq_mul_inv]
          linarith
        have hc1 : Continuous fun t => G (Q1 * t + r1) := by fun_prop
        have hc2 : Continuous fun t => G (Q2 * t + r2) := by fun_prop
        have hc3 : Continuous fun t => G ((a*Q1+b*Q2) * t + (a*r1+b*r2)) := by fun_prop
        have h2 : ∫ t in (0:ℝ)..1, G ((a*Q1+b*Q2) * t + (a*r1+b*r2)) ≤
            a * (∫ t in (0:ℝ)..1, G (Q1*t+r1)) + b * ∫ t in (0:ℝ)..1, G (Q2 * t + r2) := by
          rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
            ← intervalIntegral.integral_add ((hc1.const_mul a).intervalIntegrable 0 1)
              ((hc2.const_mul b).intervalIntegrable 0 1)]
          apply intervalIntegral.integral_mono_on zero_le_one (hc3.intervalIntegrable 0 1)
            (((hc1.const_mul a).add (hc2.const_mul b)).intervalIntegrable 0 1)
          intro t _
          have := hGcv.2 (Set.mem_univ (Q1*t+r1)) (Set.mem_univ (Q2*t+r2)) ha hb hab
          simp only [smul_eq_mul] at this
          have e : (a*Q1+b*Q2) * t + (a*r1+b*r2) = a * (Q1*t+r1) + b * (Q2*t+r2) := by ring
          rw [e]
          exact this
        linarith
    _ = a * optCost G lam K Q1 + b * optCost G lam K Q2 := rfl
