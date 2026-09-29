-- Prove2me | solution 1 for ZhengQR.OrderQty.reorder_opt_iff
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T04:47:44.442751+00:00
-- url     : https://prove2.me/submissions/3e9a09d6-63e7-4804-89d7-04ad52e6e588

import Mathlib
import Definitions.Def_ZhengQR_OrderQty_newsvendorCost
import Definitions.Def_ZhengQR_OrderQty_qrMachinery

open MeasureTheory Filter Topology

namespace ZhengQR.OrderQty

lemma aux_roi_integrable {h p : ℝ} {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hi : Integrable (fun x : ℝ => x) μ) (y : ℝ) :
    Integrable (fun x => h * max (y - x) 0 + p * max (x - y) 0) μ := by
  have h1 : Integrable (fun x : ℝ => y - x) μ := (integrable_const y).sub hi
  have h2 : Integrable (fun x : ℝ => x - y) μ := hi.sub (integrable_const y)
  exact (h1.pos_part.const_mul h).add (h2.pos_part.const_mul p)

lemma aux_roi_convex {h p : ℝ} {μ : Measure ℝ} [IsFiniteMeasure μ]
    (hh : 0 ≤ h) (hp : 0 ≤ p)
    (hi : Integrable (fun x : ℝ => x) μ) :
    ConvexOn ℝ Set.univ (newsvendorCost h p μ) := by
  refine ⟨convex_univ, ?_⟩
  intro y1 _ y2 _ a b ha hb hab
  simp only [smul_eq_mul, newsvendorCost]
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add]
  · apply integral_mono (aux_roi_integrable hi _)
    · exact ((aux_roi_integrable hi y1).const_mul a).add
        ((aux_roi_integrable hi y2).const_mul b)
    · intro x
      have hx : x = a * x + b * x := by rw [← add_mul, hab, one_mul]
      have k1 : max (a * y1 + b * y2 - x) 0 ≤ a * max (y1 - x) 0 + b * max (y2 - x) 0 := by
        apply max_le
        · have := mul_le_mul_of_nonneg_left (le_max_left (y1 - x) 0) ha
          have := mul_le_mul_of_nonneg_left (le_max_left (y2 - x) 0) hb
          linarith
        · exact add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))
      have k2 : max (x - (a * y1 + b * y2)) 0 ≤ a * max (x - y1) 0 + b * max (x - y2) 0 := by
        apply max_le
        · have := mul_le_mul_of_nonneg_left (le_max_left (x - y1) 0) ha
          have := mul_le_mul_of_nonneg_left (le_max_left (x - y2) 0) hb
          linarith
        · exact add_nonneg (mul_nonneg ha (le_max_right _ _)) (mul_nonneg hb (le_max_right _ _))
      have := mul_le_mul_of_nonneg_left k1 hh
      have := mul_le_mul_of_nonneg_left k2 hp
      simp only
      linarith
  · exact (aux_roi_integrable hi y1).const_mul a
  · exact (aux_roi_integrable hi y2).const_mul b

lemma aux_roi_main {G : ℝ → ℝ} (hcv : ConvexOn ℝ Set.univ G) (y0 : ℝ)
    (hy0 : IsMinimizer G y0) {lam K Q : ℝ} (hQ : 0 < Q) :
    IsOptReorder G lam K Q (optReorder G Q) ∧
    ∀ r : ℝ, IsOptReorder G lam K Q r ↔ G r = G (r + Q) := by
  have hGc : Continuous G := continuousOn_univ.mp (hcv.continuousOn isOpen_univ)
  -- the secant difference is monotone
  have hmono : Monotone (fun s => G (s + Q) - G s) := by
    intro s s' hss'
    simp only
    have hd : 0 < s' - s + Q := by linarith
    have ha : 0 ≤ Q / (s' - s + Q) := div_nonneg hQ.le hd.le
    have hb : 0 ≤ (s' - s) / (s' - s + Q) := div_nonneg (by linarith) hd.le
    have hab : Q / (s' - s + Q) + (s' - s) / (s' - s + Q) = 1 := by
      field_simp; ring
    have k1 := hcv.2 (Set.mem_univ s) (Set.mem_univ (s' + Q)) ha hb hab
    have k2 := hcv.2 (Set.mem_univ s) (Set.mem_univ (s' + Q)) hb ha (by linarith)
    have e1 : (Q / (s' - s + Q)) • s + ((s' - s) / (s' - s + Q)) • (s' + Q) = s' := by
      simp only [smul_eq_mul]; field_simp; ring
    have e2 : ((s' - s) / (s' - s + Q)) • s + (Q / (s' - s + Q)) • (s' + Q) = s + Q := by
      simp only [smul_eq_mul]; field_simp; ring
    rw [e1] at k1
    rw [e2] at k2
    simp only [smul_eq_mul] at k1 k2
    have hs1 : Q / (s' - s + Q) * G s + (s' - s) / (s' - s + Q) * G s = G s := by
      rw [← add_mul, hab, one_mul]
    have hs2 : Q / (s' - s + Q) * G (s' + Q) + (s' - s) / (s' - s + Q) * G (s' + Q)
        = G (s' + Q) := by
      rw [← add_mul, hab, one_mul]
    linarith
  -- derivative of r ↦ ∫_r^{r+Q} G
  have hderiv : ∀ r, HasDerivAt (fun r => ∫ y in r..r + Q, G y) (G (r + Q) - G r) r := by
    intro r
    have hΦ : ∀ u, HasDerivAt (fun u => ∫ x in (0:ℝ)..u, G x) (G u) u :=
      fun u => (hGc.integral_hasStrictDerivAt 0 u).hasDerivAt
    have hFeq : (fun r => ∫ y in r..r + Q, G y)
        = fun r => (∫ x in (0:ℝ)..(r + Q), G x) - ∫ x in (0:ℝ)..r, G x := by
      funext r
      rw [intervalIntegral.integral_interval_sub_left (hGc.intervalIntegrable _ _)
        (hGc.intervalIntegrable _ _)]
    rw [hFeq]
    exact ((hΦ (r + Q)).comp_add_const r Q).sub (hΦ r)
  have hcontF : Continuous (fun r => ∫ y in r..r + Q, G y) :=
    continuous_iff_continuousAt.2 fun x => (hderiv x).continuousAt
  have hmin_iff : ∀ r, (∀ r', (∫ y in r..r + Q, G y) ≤ ∫ y in r'..r' + Q, G y) ↔
      G r = G (r + Q) := by
    intro r
    constructor
    · intro hmin
      have hlm : IsLocalMin (fun r => ∫ y in r..r + Q, G y) r :=
        Filter.Eventually.of_forall hmin
      have := hlm.hasDerivAt_eq_zero (hderiv r)
      linarith
    · intro heq r'
      rcases le_total r r' with hrr | hrr
      · have hmo : MonotoneOn (fun r => ∫ y in r..r + Q, G y) (Set.Ici r) := by
          apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici r) hcontF.continuousOn
            (fun x _ => (hderiv x).hasDerivWithinAt)
          intro x hx
          rw [interior_Ici] at hx
          have := hmono (le_of_lt (Set.mem_Ioi.mp hx))
          simp only at this
          linarith
        exact hmo (Set.mem_Ici.2 le_rfl) hrr hrr
      · have hmo : AntitoneOn (fun r => ∫ y in r..r + Q, G y) (Set.Iic r) := by
          apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Iic r) hcontF.continuousOn
            (fun x _ => (hderiv x).hasDerivWithinAt)
          intro x hx
          rw [interior_Iic] at hx
          have := hmono (le_of_lt (Set.mem_Iio.mp hx))
          simp only at this
          linarith
        exact hmo hrr (Set.mem_Iic.2 le_rfl) hrr
  have hopt_iff : ∀ r, IsOptReorder G lam K Q r ↔
      ∀ r', (∫ y in r..r + Q, G y) ≤ ∫ y in r'..r' + Q, G y := by
    intro r
    unfold IsOptReorder qrCost
    constructor
    · intro H r'
      have := H r'
      rw [div_le_div_iff_of_pos_right hQ] at this
      linarith
    · intro H r'
      rw [div_le_div_iff_of_pos_right hQ]
      linarith [H r']
  -- existence of a zero of the secant difference (IVT)
  obtain ⟨c, hc⟩ : ∃ c, G (c + Q) - G c = 0 := by
    have hcont : ContinuousOn (fun s => G (s + Q) - G s) (Set.Icc (y0 - Q) y0) :=
      ((hGc.comp (continuous_add_const Q)).sub hGc).continuousOn
    have hle : y0 - Q ≤ y0 := by linarith
    have h0 : (0:ℝ) ∈ Set.Icc (G (y0 - Q + Q) - G (y0 - Q)) (G (y0 + Q) - G y0) := by
      constructor
      · have := hy0 (y0 - Q)
        rw [sub_add_cancel]
        linarith
      · have := hy0 (y0 + Q)
        linarith
    obtain ⟨c, _, hc⟩ := intermediate_value_Icc hle hcont h0
    exact ⟨c, hc⟩
  have hex : ∃ r, ∀ r' : ℝ, (∫ y in r..r + Q, G y) ≤ ∫ y in r'..r' + Q, G y :=
    ⟨c, (hmin_iff c).2 (by linarith)⟩
  refine ⟨?_, fun r => (hopt_iff r).trans (hmin_iff r)⟩
  rw [hopt_iff]
  unfold optReorder
  rw [dif_pos hex]
  exact hex.choose_spec

end ZhengQR.OrderQty

open ZhengQR.OrderQty
open MeasureTheory Filter Topology

theorem solution
    {lam L K h p : ℝ} {μ : Measure ℝ}
    (hlam : 0 < lam) (hL : 0 < L) (hK : 0 < K) (hh : 0 < h) (hp : 0 < p)
    (hμ : IsLeadtimeDemand lam L μ)
    (hG : ∃! y : ℝ, IsMinimizer (newsvendorCost h p μ) y)
    {Q : ℝ} (hQ : 0 < Q) :
    IsOptReorder (newsvendorCost h p μ) lam K Q (optReorder (newsvendorCost h p μ) Q) ∧
    ∀ r : ℝ, IsOptReorder (newsvendorCost h p μ) lam K Q r ↔
      newsvendorCost h p μ r = newsvendorCost h p μ (r + Q) := by
  have := hμ.isProb
  obtain ⟨y0, hy0, _⟩ := hG
  exact aux_roi_main (aux_roi_convex hh.le hp.le hμ.integrable) y0 hy0 hQ
