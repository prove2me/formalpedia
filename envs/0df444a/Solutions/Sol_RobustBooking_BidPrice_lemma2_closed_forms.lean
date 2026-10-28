-- Prove2me | solution 1 for RobustBooking.BidPrice.lemma2_closed_forms
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T16:40:42.923906+00:00
-- url     : https://prove2.me/submissions/049480f9-be90-43ea-a431-889edf4eb50a

import Mathlib
import Definitions.Def_RobustBooking_BidPrice_Model
import Definitions.Def_RobustBooking_BidPrice_Policy
import Definitions.Def_RobustBooking_BidPrice_Controls

open RobustBooking.BidPrice in
theorem solution (fmin fmax n : ℝ) (hfmin : 0 < fmin) (hf : fmin < fmax)
    (hn : 0 < n) (q : ℝ) :
    (0 ≤ q → q < n * rho (discountRatio fmin fmax) →
      bidPriceP fmin fmax n q = fmin ∧ valueAccumulation fmin fmax n q = q * fmin) ∧
    (n * rho (discountRatio fmin fmax) ≤ q → q ≤ n →
      bidPriceP fmin fmax n q =
          fmax * discountRatio fmin fmax ^
            ((n - q) / (n * (1 - rho (discountRatio fmin fmax)))) ∧
        valueAccumulation fmin fmax n q =
          n * bidPriceP fmin fmax n q / (1 - Real.log (discountRatio fmin fmax))) := by
  have hfmax : 0 < fmax := lt_trans hfmin hf
  obtain ⟨r, hrdef⟩ : ∃ r, r = discountRatio fmin fmax := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hrdef]; exact div_pos hfmin hfmax
  have hr1 : r < 1 := by rw [hrdef]; exact (div_lt_one hfmax).mpr hf
  have hrf : fmax * r = fmin := by rw [hrdef, discountRatio]; field_simp
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log r := ⟨_, rfl⟩
  have hL : L < 0 := by rw [hLdef]; exact Real.log_neg hr0 hr1
  have hLdiff : Real.log fmax - Real.log fmin = -L := by
    rw [hLdef, hrdef, discountRatio, Real.log_div hfmin.ne' hfmax.ne']; ring
  have h1L : 0 < 1 - L := by linarith
  obtain ⟨ρ, hρdef⟩ : ∃ ρ, ρ = rho r := ⟨_, rfl⟩
  have hρ : ρ = 1 / (1 - L) := by rw [hρdef, hLdef]; rfl
  have hρL : ρ * (1 - L) = 1 := by rw [hρ]; field_simp
  have hρpos : 0 < ρ := by rw [hρ]; positivity
  obtain ⟨c, hc⟩ : ∃ c, c = n * (1 - ρ) := ⟨_, rfl⟩
  have hcρ : c = -(n * ρ * L) := by rw [hc]; linear_combination (-n) * hρL
  have hcpos : 0 < c := by rw [hcρ]; nlinarith
  have hcL : c * (1 - L) = -(L * n) := by rw [hcρ]; linear_combination (-(n * L)) * hρL
  rw [← hrdef, ← hρdef, ← hc, ← hLdef]
  -- closed form of the protection level
  have hQ : ∀ f, protectionControl fmin fmax n f =
      n - (Real.log fmax - Real.log f) * n / (1 - L) := by
    intro f
    unfold protectionControl theta
    rw [hLdiff, ← hrdef, ← hLdef]
    have hLne : L ≠ 0 := hL.ne
    field_simp
    ring
  -- bid price below the threshold
  have P1 : ∀ s, s ≤ n * ρ → bidPriceP fmin fmax n s = fmin := by
    intro s hs
    unfold bidPriceP orderQuantityControl
    apply IsLeast.csInf_eq
    refine ⟨⟨⟨le_rfl, hf.le⟩, ?_⟩, fun f hf' => hf'.1.1⟩
    rw [hQ, hLdiff]
    have : -L * n / (1 - L) = n - n * ρ := by
      rw [div_eq_iff h1L.ne']
      linear_combination n * hρL
    linarith
  -- bid price above the threshold
  let g2 : ℝ → ℝ := fun s => fmax * r ^ ((n - s) / c)
  have hlog2 : ∀ s, Real.log (g2 s) = Real.log fmax + (n - s) / c * L := by
    intro s
    simp only [g2]
    rw [Real.log_mul hfmax.ne' (Real.rpow_pos_of_pos hr0 _).ne', Real.log_rpow hr0, hLdef]
  have hg2pos : ∀ s, 0 < g2 s := fun s => mul_pos hfmax (Real.rpow_pos_of_pos hr0 _)
  have hLn : L * n = -(c * (1 - L)) := by linarith [hcL]
  have hkey : ∀ s, (n - s) / c * L * n = -((n - s) * (1 - L)) := by
    intro s
    calc (n - s) / c * L * n = (n - s) / c * (L * n) := by ring
      _ = -((n - s) * (1 - L)) * (c / c) := by rw [hLn]; ring
      _ = -((n - s) * (1 - L)) := by rw [div_self hcpos.ne', mul_one]
  have P2 : ∀ s, n * ρ ≤ s → s ≤ n → bidPriceP fmin fmax n s = g2 s := by
    intro s hs1 hs2
    have he0 : 0 ≤ (n - s) / c := div_nonneg (by linarith) hcpos.le
    have he1 : (n - s) / c ≤ 1 := by
      rw [div_le_one hcpos, hc]; nlinarith
    unfold bidPriceP orderQuantityControl
    apply IsLeast.csInf_eq
    constructor
    · refine ⟨⟨?_, ?_⟩, ?_⟩
      · rw [← Real.log_le_log_iff hfmin (hg2pos s), hlog2]
        have : Real.log fmin = Real.log fmax + L := by linarith
        rw [this]
        nlinarith
      · rw [← Real.log_le_log_iff (hg2pos s) hfmax, hlog2]
        nlinarith
      · rw [hQ, hlog2]
        have : (Real.log fmax - (Real.log fmax + (n - s) / c * L)) * n / (1 - L) = n - s := by
          calc (Real.log fmax - (Real.log fmax + (n - s) / c * L)) * n / (1 - L)
              = -((n - s) / c * L * n) / (1 - L) := by ring
            _ = (n - s) * ((1 - L) / (1 - L)) := by rw [hkey]; ring
            _ = n - s := by rw [div_self h1L.ne', mul_one]
        linarith
    · intro f ⟨⟨hf1, hf2⟩, hfs⟩
      have hfpos : 0 < f := lt_of_lt_of_le hfmin hf1
      rw [← Real.log_le_log_iff (hg2pos s) hfpos, hlog2]
      rw [hQ] at hfs
      have h3 : (Real.log fmax - Real.log f) * n / (1 - L) ≤ n - s := by linarith
      rw [div_le_iff₀ h1L] at h3
      have h4 := hkey s
      nlinarith
  constructor
  · intro hq0 hq
    have hb : bidPriceP fmin fmax n q = fmin := P1 q hq.le
    refine ⟨hb, ?_⟩
    unfold valueAccumulation
    rw [intervalIntegral.integral_congr (g := fun _ => fmin) (fun s hs => by
      rw [Set.uIcc_of_le hq0] at hs
      exact P1 s (by linarith [hs.2]))]
    simp
  · intro hq1 hq2
    have hb : bidPriceP fmin fmax n q = g2 q := P2 q hq1 hq2
    refine ⟨hb, ?_⟩
    obtain ⟨a, ha⟩ : ∃ a, a = n * ρ := ⟨_, rfl⟩
    rw [← ha] at hq1
    have ha0 : 0 ≤ a := by rw [ha]; positivity
    have hint1 : IntervalIntegrable (bidPriceP fmin fmax n) MeasureTheory.volume 0 a := by
      rw [intervalIntegrable_congr (g := fun _ => fmin) (fun s hs => by
        rw [Set.uIoc_of_le ha0] at hs
        exact P1 s (ha ▸ hs.2))]
      exact intervalIntegrable_const
    have hg2c : Continuous g2 := by
      simp only [g2]
      exact continuous_const.mul ((Real.continuous_const_rpow hr0.ne').comp
        ((continuous_const.sub continuous_id).div_const c))
    have hint2 : IntervalIntegrable (bidPriceP fmin fmax n) MeasureTheory.volume a q := by
      rw [intervalIntegrable_congr (g := g2) (fun s hs => by
        rw [Set.uIoc_of_le hq1] at hs
        exact P2 s (ha ▸ hs.1.le) (le_trans hs.2 hq2))]
      exact hg2c.intervalIntegrable _ _
    unfold valueAccumulation
    rw [← intervalIntegral.integral_add_adjacent_intervals hint1 hint2]
    rw [intervalIntegral.integral_congr (a := 0) (b := a) (g := fun _ => fmin) (fun s hs => by
      rw [Set.uIcc_of_le ha0] at hs
      exact P1 s (ha ▸ hs.2))]
    rw [intervalIntegral.integral_congr (a := a) (b := q) (g := g2) (fun s hs => by
      rw [Set.uIcc_of_le hq1] at hs
      exact P2 s (ha ▸ hs.1) (le_trans hs.2 hq2))]
    -- antiderivative
    let F : ℝ → ℝ := fun s => a * g2 s
    have hF : ∀ s, HasDerivAt F (g2 s) s := by
      intro s
      have h1 : HasDerivAt (fun x : ℝ => (n - x) / c) ((-1) / c) s :=
        ((hasDerivAt_id s).const_sub n).div_const c
      have h2 := (Real.hasStrictDerivAt_const_rpow hr0 ((n - s) / c)).hasDerivAt.comp s h1
      have h3 := (h2.const_mul fmax).const_mul a
      refine h3.congr_deriv ?_
      simp only [g2]
      rw [← hLdef]
      calc a * (fmax * (r ^ ((n - s) / c) * L * (-1 / c)))
          = fmax * r ^ ((n - s) / c) * (-(a * L) / c) := by ring
        _ = fmax * r ^ ((n - s) / c) * (c / c) := by rw [ha, ← hcρ]
        _ = fmax * r ^ ((n - s) / c) := by rw [div_self hcpos.ne', mul_one]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hF s)
      (hg2c.intervalIntegrable _ _)]
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
    have hga : g2 a = fmin := by
      simp only [g2]
      have : (n - a) / c = 1 := by
        rw [div_eq_one_iff_eq hcpos.ne', ha, hc]; ring
      rw [this, Real.rpow_one, hrf]
    simp only [F]
    rw [hga, hb]
    have : a = n / (1 - L) := by rw [ha, hρ]; ring
    rw [this]
    ring
