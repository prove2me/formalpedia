-- Prove2me | solution 1 for ZhengQR.EOQHeuristic.reorder_opt_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:10:40.223898+00:00
-- url     : https://prove2.me/submissions/5ffd7059-4afd-42c8-80f5-b0be9afcb9df

import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic

lemma aux_roi_integrable {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (y : ℝ) :
    Integrable (fun x : ℝ => h * max (y - x) 0 + p * max (x - y) 0) μ := by
  have := hM.isProb
  exact (((integrable_const y).sub hM.integrable).pos_part.const_mul h).add
    ((hM.integrable.sub (integrable_const y)).pos_part.const_mul p)

lemma aux_roi_pt {h p a b y1 y2 x : ℝ} (hh : 0 ≤ h) (hp : 0 ≤ p) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) :
    h * max (a * y1 + b * y2 - x) 0 + p * max (x - (a * y1 + b * y2)) 0 ≤
      a * (h * max (y1 - x) 0 + p * max (x - y1) 0) +
        b * (h * max (y2 - x) 0 + p * max (x - y2) 0) := by
  have e1 : max (a * y1 + b * y2 - x) 0 ≤ a * max (y1 - x) 0 + b * max (y2 - x) 0 := by
    apply max_le
    · have : a * y1 + b * y2 - x = a * (y1 - x) + b * (y2 - x) := by
        have : x = a * x + b * x := by rw [← add_mul, hab, one_mul]
        linarith
      rw [this]
      exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
    · exact add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))
  have e2 : max (x - (a * y1 + b * y2)) 0 ≤ a * max (x - y1) 0 + b * max (x - y2) 0 := by
    apply max_le
    · have : x - (a * y1 + b * y2) = a * (x - y1) + b * (x - y2) := by
        have : x = a * x + b * x := by rw [← add_mul, hab, one_mul]
        linarith
      rw [this]
      exact add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) ha)
        (mul_le_mul_of_nonneg_left (le_max_left _ _) hb)
    · exact add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))
  have f1 := mul_le_mul_of_nonneg_left e1 hh
  have f2 := mul_le_mul_of_nonneg_left e2 hp
  nlinarith [f1, f2]

lemma aux_roi_convex {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) :
    ConvexOn ℝ Set.univ (newsvendorCost μ h p) := by
  refine ⟨convex_univ, ?_⟩
  intro y1 _ y2 _ a b ha hb hab
  simp only [newsvendorCost, smul_eq_mul]
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add ((aux_roi_integrable hM y1).const_mul a)
      ((aux_roi_integrable hM y2).const_mul b)]
  apply integral_mono (aux_roi_integrable hM _)
    (((aux_roi_integrable hM y1).const_mul a).add ((aux_roi_integrable hM y2).const_mul b))
  intro x
  exact aux_roi_pt hM.h_pos.le hM.p_pos.le ha hb hab

lemma aux_roi_cont {lam L h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) :
    Continuous (newsvendorCost μ h p) := by
  have := (aux_roi_convex hM).continuousOn isOpen_univ
  exact continuousOn_univ.mp this

/-- For a convex function, the increment over a window of fixed length `Q` is monotone. -/
lemma aux_roi_mono {G : ℝ → ℝ} (hG : ConvexOn ℝ Set.univ G) {Q : ℝ} (hQ : 0 < Q) {r r' : ℝ}
    (hrr : r ≤ r') : G (r + Q) - G r ≤ G (r' + Q) - G r' := by
  have hsQ : 0 < Q + (r' - r) := by linarith
  have ht0 : 0 ≤ Q / (Q + (r' - r)) := div_nonneg hQ.le hsQ.le
  have ht1 : Q / (Q + (r' - r)) ≤ 1 := (div_le_one hsQ).mpr (by linarith)
  have h1 := hG.2 (Set.mem_univ r) (Set.mem_univ (r' + Q)) (sub_nonneg.mpr ht1) ht0 (by ring)
  have h2 := hG.2 (Set.mem_univ r) (Set.mem_univ (r' + Q)) ht0 (sub_nonneg.mpr ht1) (by ring)
  simp only [smul_eq_mul] at h1 h2
  have e1 : (1 - Q / (Q + (r' - r))) * r + Q / (Q + (r' - r)) * (r' + Q) = r + Q := by
    field_simp
    ring
  have e2 : Q / (Q + (r' - r)) * r + (1 - Q / (Q + (r' - r))) * (r' + Q) = r' := by
    field_simp
    ring
  rw [e1] at h1
  rw [e2] at h2
  linarith

end ZhengQR.EOQHeuristic

open ZhengQR.EOQHeuristic

open MeasureTheory Filter Topology

theorem solution {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) (Q : ℝ) (hQ : 0 < Q) :
    (∃ r : ℝ, IsOptReorder (newsvendorCost μ h p) lam K Q r) ∧
      ∀ r : ℝ, IsOptReorder (newsvendorCost μ h p) lam K Q r ↔ newsvendorCost μ h p r = newsvendorCost μ h p (r + Q) := by
  set G := newsvendorCost μ h p with hGdef
  have hGc : Continuous G := aux_roi_cont hM
  have hGcv : ConvexOn ℝ Set.univ G := aux_roi_convex hM
  set F : ℝ → ℝ := fun r => ∫ y in r..r + Q, G y with hF
  have hopt : ∀ r, IsOptReorder G lam K Q r ↔ ∀ r', F r ≤ F r' := by
    intro r
    unfold IsOptReorder qrCost
    constructor
    · intro H r'
      have := (div_le_div_iff_of_pos_right hQ).mp (H r')
      simp only [hF]
      linarith
    · intro H r'
      apply div_le_div_of_nonneg_right _ hQ.le
      have := H r'
      simp only [hF] at this
      linarith
  have hi : ∀ a b, IntervalIntegrable G volume a b := fun a b => hGc.intervalIntegrable a b
  have hdiff : ∀ r r', F r' - F r = ∫ x in r..r', (G (x + Q) - G x) := by
    intro r r'
    simp only [hF]
    have hiQ : IntervalIntegrable (fun x => G (x + Q)) volume r r' :=
      (hGc.comp (continuous_id.add continuous_const)).intervalIntegrable _ _
    rw [intervalIntegral.integral_sub hiQ (hi _ _)]
    rw [intervalIntegral.integral_comp_add_right G Q]
    have h1 := intervalIntegral.integral_add_adjacent_intervals (hi r (r + Q)) (hi (r + Q) (r' + Q))
    have h2 := intervalIntegral.integral_add_adjacent_intervals (hi r r') (hi r' (r' + Q))
    linarith
  have hderiv : ∀ r, HasDerivAt F (G (r + Q) - G r) r := by
    intro r
    have hd1 : HasDerivAt (fun u => ∫ x in (0 : ℝ)..u, G x) (G (r + Q)) (r + Q) :=
      (hGc.integral_hasStrictDerivAt 0 (r + Q)).hasDerivAt
    have hd1' : HasDerivAt (fun u => ∫ x in (0 : ℝ)..(u + Q), G x) (G (r + Q)) r := by
      have := hd1.comp r ((hasDerivAt_id r).add_const Q)
      simp only [mul_one, id] at this
      exact this
    have hd2 : HasDerivAt (fun u => ∫ x in (0 : ℝ)..u, G x) (G r) r :=
      (hGc.integral_hasStrictDerivAt 0 r).hasDerivAt
    have heq : F = fun u => (∫ x in (0 : ℝ)..(u + Q), G x) - ∫ x in (0 : ℝ)..u, G x := by
      funext u
      simp only [hF]
      rw [intervalIntegral.integral_interval_sub_left (hi _ _) (hi _ _)]
    rw [heq]
    exact hd1'.sub hd2
  have hsuff : ∀ r, G r = G (r + Q) → ∀ r', F r ≤ F r' := by
    intro r hr r'
    have hd := hdiff r r'
    rcases le_total r r' with hle | hle
    · have : 0 ≤ ∫ x in r..r', (G (x + Q) - G x) := by
        apply intervalIntegral.integral_nonneg hle
        intro x hx
        have := aux_roi_mono hGcv hQ hx.1
        linarith
      linarith
    · have : 0 ≤ ∫ x in r'..r, (G x - G (x + Q)) := by
        apply intervalIntegral.integral_nonneg hle
        intro x hx
        have := aux_roi_mono hGcv hQ hx.2
        linarith
      have e : (∫ x in r..r', (G (x + Q) - G x)) = ∫ x in r'..r, (G x - G (x + Q)) := by
        rw [intervalIntegral.integral_symm, ← intervalIntegral.integral_neg]
        congr 1
        funext x
        ring
      linarith
  have hnec : ∀ r, (∀ r', F r ≤ F r') → G r = G (r + Q) := by
    intro r H
    have hmin : IsLocalMin F r := Filter.Eventually.of_forall H
    have := hmin.hasDerivAt_eq_zero (hderiv r)
    linarith
  refine ⟨?_, fun r => (hopt r).trans ⟨hnec r, hsuff r⟩⟩
  obtain ⟨y0, hy0, -⟩ := hM.unique_min
  have hφc : Continuous (fun x => G (x + Q) - G x) :=
    (hGc.comp (continuous_id.add continuous_const)).sub hGc
  have hab : y0 - Q ≤ y0 := by linarith
  have hmem : (0 : ℝ) ∈ Set.Icc ((fun x => G (x + Q) - G x) (y0 - Q))
      ((fun x => G (x + Q) - G x) y0) := by
    constructor
    · simp only [sub_add_cancel]
      linarith [hy0 (y0 - Q)]
    · simp only
      linarith [hy0 (y0 + Q)]
  obtain ⟨r, -, hr⟩ := intermediate_value_Icc hab hφc.continuousOn hmem
  refine ⟨r, (hopt r).mpr (hsuff r ?_)⟩
  simp only at hr
  linarith
