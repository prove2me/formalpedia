-- Prove2me | solution 1 for ZhengQR.EOQHeuristic.reorderPt_cost_le_max
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:28:41.812702+00:00
-- url     : https://prove2.me/submissions/29bee434-aec3-4e9d-be3b-75be7345d957

import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic

lemma aux_rpc_integrable {h p : ℝ} {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hI : Integrable (fun x : ℝ => x) μ) (y : ℝ) :
    Integrable (fun x => h * max (y - x) 0 + p * max (x - y) 0) μ := by
  have h1 : Integrable (fun x : ℝ => y - x) μ := (integrable_const y).sub hI
  have h2 : Integrable (fun x : ℝ => x - y) μ := hI.sub (integrable_const y)
  exact (h1.pos_part.const_mul h).add (h2.pos_part.const_mul p)

lemma aux_rpc_convex {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) :
    ConvexOn ℝ Set.univ (newsvendorCost μ h p) := by
  have := hM.isProb
  refine ⟨convex_univ, fun y1 _ y2 _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul, newsvendorCost]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add]
  · apply integral_mono (aux_rpc_integrable hM.integrable _)
    · exact ((aux_rpc_integrable hM.integrable y1).const_mul a).add
        ((aux_rpc_integrable hM.integrable y2).const_mul b)
    · intro x
      have e1 := le_max_left (y1 - x) 0
      have e2 := le_max_left (y2 - x) 0
      have e3 := le_max_left (x - y1) 0
      have e4 := le_max_left (x - y2) 0
      have f1 := le_max_right (y1 - x) 0
      have f2 := le_max_right (y2 - x) 0
      have f3 := le_max_right (x - y1) 0
      have f4 := le_max_right (x - y2) 0
      have k1 : max (a * y1 + b * y2 - x) 0 ≤ a * max (y1 - x) 0 + b * max (y2 - x) 0 := by
        apply max_le
        · have : a * y1 + b * y2 - x = a * (y1 - x) + b * (y2 - x) := by
            linear_combination x * hab
          rw [this]
          nlinarith [mul_le_mul_of_nonneg_left e1 ha, mul_le_mul_of_nonneg_left e2 hb]
        · positivity
      have k2 : max (x - (a * y1 + b * y2)) 0 ≤ a * max (x - y1) 0 + b * max (x - y2) 0 := by
        apply max_le
        · have : x - (a * y1 + b * y2) = a * (x - y1) + b * (x - y2) := by
            linear_combination (-x) * hab
          rw [this]
          nlinarith [mul_le_mul_of_nonneg_left e3 ha, mul_le_mul_of_nonneg_left e4 hb]
        · positivity
      nlinarith [mul_le_mul_of_nonneg_left k1 hM.h_pos.le, mul_le_mul_of_nonneg_left k2 hM.p_pos.le]
  · exact (aux_rpc_integrable hM.integrable y1).const_mul a
  · exact (aux_rpc_integrable hM.integrable y2).const_mul b

lemma aux_rpc_lb1 {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (y : ℝ) :
    h * (y - lam * L) ≤ newsvendorCost μ h p y := by
  have := hM.isProb
  have hint : Integrable (fun x : ℝ => y - x) μ := (integrable_const y).sub hM.integrable
  have : h * (y - lam * L) = ∫ x, h * (y - x) ∂μ := by
    rw [integral_const_mul, integral_sub (integrable_const y) hM.integrable, integral_const,
      hM.mean]
    simp
  rw [this]
  apply integral_mono (hint.const_mul h) (aux_rpc_integrable hM.integrable y)
  intro x
  have := le_max_left (y - x) 0
  have := le_max_right (x - y) 0
  nlinarith [hM.h_pos, hM.p_pos]

lemma aux_rpc_lb2 {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (y : ℝ) :
    p * (lam * L - y) ≤ newsvendorCost μ h p y := by
  have := hM.isProb
  have hint : Integrable (fun x : ℝ => x - y) μ := hM.integrable.sub (integrable_const y)
  have : p * (lam * L - y) = ∫ x, p * (x - y) ∂μ := by
    rw [integral_const_mul, integral_sub hM.integrable (integrable_const y), integral_const,
      hM.mean]
    simp
  rw [this]
  apply integral_mono (hint.const_mul p) (aux_rpc_integrable hM.integrable y)
  intro x
  have := le_max_right (y - x) 0
  have := le_max_left (x - y) 0
  nlinarith [hM.h_pos, hM.p_pos]

end ZhengQR.EOQHeuristic

open ZhengQR.EOQHeuristic

theorem solution {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) :
    ∀ Q : ℝ, 0 < Q → ∀ r : ℝ,
      newsvendorCost μ h p (reorderPt (newsvendorCost μ h p) lam K Q) ≤ max (newsvendorCost μ h p r) (newsvendorCost μ h p (r + Q)) := by
  intro Q hQ r
  have hconv := aux_rpc_convex hM
  have lb1 := aux_rpc_lb1 hM
  have lb2 := aux_rpc_lb2 hM
  have hh := hM.h_pos
  have hp := hM.p_pos
  set G := newsvendorCost μ h p with hG
  have hcont : Continuous G := continuousOn_univ.mp (hconv.continuousOn isOpen_univ)
  set P : ℝ → ℝ := fun u => ∫ x in (0:ℝ)..u, G x with hPdef
  have hP : ∀ u, HasDerivAt P (G u) u := fun u => (hcont.integral_hasStrictDerivAt 0 u).hasDerivAt
  set I : ℝ → ℝ := fun r => ∫ y in r..r + Q, G y with hIdef
  have hIP : I = fun r => P (r + Q) - P r := by
    funext r
    simp only [I, P]
    rw [intervalIntegral.integral_interval_sub_left (μ := volume) (hcont.intervalIntegrable _ _)
      (hcont.intervalIntegrable _ _)]
  have hI' : ∀ r, HasDerivAt I (G (r + Q) - G r) r := by
    intro r
    rw [hIP]
    exact ((hP (r + Q)).comp_add_const r Q).sub (hP r)
  have hIcont : Continuous I := continuous_iff_continuousAt.2 fun r => (hI' r).continuousAt
  have b1 : ∀ r, Q * (h * (r - lam * L)) ≤ I r := by
    intro r
    have := intervalIntegral.integral_mono_on (μ := volume) (a := r) (b := r + Q) (by linarith)
      (intervalIntegrable_const (c := h * (r - lam * L))) (hcont.intervalIntegrable _ _)
      (fun x hx => le_trans (by nlinarith [hx.1]) (lb1 x))
    rw [intervalIntegral.integral_const, smul_eq_mul, show r + Q - r = Q by ring] at this
    exact this
  have b2 : ∀ r, Q * (p * (lam * L - r - Q)) ≤ I r := by
    intro r
    have := intervalIntegral.integral_mono_on (μ := volume) (a := r) (b := r + Q) (by linarith)
      (intervalIntegrable_const (c := p * (lam * L - r - Q))) (hcont.intervalIntegrable _ _)
      (fun x hx => le_trans (by nlinarith [hx.2]) (lb2 x))
    rw [intervalIntegral.integral_const, smul_eq_mul, show r + Q - r = Q by ring] at this
    exact this
  have hlim : Tendsto I (cocompact ℝ) atTop := by
    rw [cocompact_eq_atBot_atTop, tendsto_sup]
    constructor
    · have : Tendsto (fun r : ℝ => Q * p * (-r) + Q * p * (lam * L - Q)) atBot atTop :=
        tendsto_atTop_add_const_right _ _ (tendsto_neg_atBot_atTop.const_mul_atTop (mul_pos hQ hp))
      refine tendsto_atTop_mono (fun r => ?_) this
      have := b2 r
      linarith [show Q * p * (-r) + Q * p * (lam * L - Q) = Q * (p * (lam * L - r - Q)) by ring]
    · have : Tendsto (fun r : ℝ => Q * h * r + Q * h * (-(lam * L))) atTop atTop :=
        tendsto_atTop_add_const_right _ _ (tendsto_id.const_mul_atTop (mul_pos hQ hh))
      refine tendsto_atTop_mono (fun r => ?_) this
      have := b1 r
      linarith [show Q * h * r + Q * h * (-(lam * L)) = Q * (h * (r - lam * L)) by ring]
  obtain ⟨r0, hr0⟩ := hIcont.exists_forall_le hlim
  have hex : ∃ r, IsOptReorder G lam K Q r := by
    refine ⟨r0, fun r' => ?_⟩
    unfold qrCost
    exact div_le_div_of_nonneg_right (by linarith [hr0 r']) hQ.le
  have hopt : IsOptReorder G lam K Q (reorderPt G lam K Q) := by
    unfold reorderPt
    rw [dif_pos hex]
    exact hex.choose_spec
  set rs := reorderPt G lam K Q with hrs
  have hmin : ∀ r', I rs ≤ I r' := by
    intro r'
    have h1 := hopt r'
    unfold qrCost at h1
    have h2 := (div_le_div_iff_of_pos_right hQ).mp h1
    simp only [I]
    linarith
  have hloc : IsLocalMin I rs := Filter.Eventually.of_forall hmin
  have heq : G (rs + Q) - G rs = 0 := hloc.hasDerivAt_eq_zero (hI' rs)
  rcases le_or_gt r rs with hle | hlt
  · have : G rs ≤ G r := hconv.le_left_of_right_le'' (Set.mem_univ _) (Set.mem_univ _) hle
      (by linarith : rs < rs + Q) (by linarith)
    exact le_max_of_le_left this
  · have : G (rs + Q) ≤ G (r + Q) := hconv.le_right_of_left_le'' (Set.mem_univ rs)
      (Set.mem_univ _) (by linarith : rs < rs + Q) (by linarith) (by linarith)
    exact le_max_of_le_right (by linarith)
