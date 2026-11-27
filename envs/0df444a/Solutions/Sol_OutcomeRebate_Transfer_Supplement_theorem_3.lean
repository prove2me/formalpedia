-- Prove2me | solution 1 for OutcomeRebate.Transfer.Supplement.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:05:50.895595+00:00
-- url     : https://prove2.me/submissions/fb854790-c46b-4671-85c4-a96e7d780a88

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model
import Definitions.Def_OutcomeRebate_Transfer_Supplement_PartialRebate

open OutcomeRebate
open OutcomeRebate.Transfer
open OutcomeRebate.Transfer.Supplement

theorem solution (P : Params) (hS : P.Standing) (θ : ℝ) (hθ : 0 ≤ θ ∧ θ ≤ 1)
    (hA : PartialAssumption P θ) :
    let m := partialMargin P θ
    let zb := zBar P θ
    let a := m - P.q * zb * P.β / 2
    let b := m - P.q * zb * (1 + P.β) / 2
    let rootP := fun p3 : ℝ => p3 ∈ Set.Icc (P.c / m) (pPartialBarStar P θ) ∧
      firmProfitP P θ 1 (pPartialBarStar P θ) = firmProfitP P θ P.β p3
    let p1 := P.q * (P.vp + P.vbar / 2) / a
    let p2 := P.q * P.vp / b
    (P.c / m ≤ P.vbar / zb → ∃! p3, rootP p3) ∧
    ((m ≤ P.β * P.q * zb / 2 ∨ pPartialStar P θ * a / P.q - P.vbar / 2 ≤ P.vp) →
      IsEqPriceP P θ (pPartialStar P θ) ∧ coversP P θ (pPartialStar P θ) ∧
      ∀ p, IsEqPriceP P θ p → p = pPartialStar P θ) ∧
    ((P.β * P.q * zb / 2 < m ∧ max (P.c / m) (P.vbar / zb) * a / P.q - P.vbar / 2 < P.vp ∧
      P.vp < pPartialStar P θ * a / P.q - P.vbar / 2) →
      IsEqPriceP P θ p1 ∧ coversP P θ p1 ∧ ∀ p, IsEqPriceP P θ p → p = p1) ∧
    (∀ p3, rootP p3 →
      ((P.c / m ≤ P.vbar / zb ∧ (1 + P.β) * P.q * zb / 2 < m ∧
        p3 * b / P.q ≤ P.vp ∧ P.vp ≤ P.vbar / zb * a / P.q - P.vbar / 2) →
        IsEqPriceP P θ p2 ∧ coversP P θ p2 ∧
        (p3 * b / P.q < P.vp → ∀ p, IsEqPriceP P θ p → p = p2)) ∧
      ((P.c / m ≤ P.vbar / zb ∧ (1 + P.β) * P.q * zb / 2 < m ∧ P.vp < p3 * b / P.q) →
        IsEqPriceP P θ (pPartialBarStar P θ) ∧ ¬coversP P θ (pPartialBarStar P θ) ∧
        (P.c / m < P.vbar / zb → ∀ p, IsEqPriceP P θ p → p = pPartialBarStar P θ))) ∧
    ((P.vbar / zb < P.c / m ∧ P.β * P.q * zb / 2 < m ∧ P.vp ≤ (P.c / P.q) * a / m - P.vbar / 2) →
      (∀ p, 0 ≤ p → realizedProfitP P θ p ≤ 0) ∧ (∃ p, 0 ≤ p ∧ realizedProfitP P θ p = 0) ∧
      (∀ p, P.c / m < p → p < P.vbar / (P.β * zb) → ¬coversP P θ p) ∧
      (P.vp < (P.c / P.q) * a / m - P.vbar / 2 → ¬coversP P θ (P.c / m))) := by
        intro m zb a b rootP p1 p2
        obtain ⟨hn, hvbar, hc, hβ0, hβ1, hq0, hq1, hα0, hα1, hlam, hvp⟩ := hS
        have hm : m = partialMargin P θ := rfl
        have hzb : zb = zBar P θ := rfl
        have ha : a = m - P.q * zb * P.β / 2 := rfl
        have hb : b = m - P.q * zb * (1 + P.β) / 2 := rfl
        have hp1 : p1 = P.q * (P.vp + P.vbar / 2) / a := rfl
        have hp2 : p2 = P.q * P.vp / b := rfl
        have hrootdef : ∀ p3, rootP p3 ↔ (p3 ∈ Set.Icc (P.c / m) (pPartialBarStar P θ) ∧
            firmProfitP P θ 1 (pPartialBarStar P θ) = firmProfitP P θ P.β p3) := fun _ => Iff.rfl
        clear_value rootP p1 p2 a b zb m
        have hK0 : 0 ≤ P.lam * (1 - P.q) / P.q :=
          div_nonneg (mul_nonneg (by linarith only [hlam]) (by linarith only [hq1])) hq0.le
        have hL : P.z - 1 = (P.lam * (1 - P.q) / P.q) ^ (1 / P.α) := by
          unfold Params.z zOf; ring
        have hL0 : 0 ≤ P.z - 1 := by rw [hL]; exact Real.rpow_nonneg hK0 _
        have hm_pos : 0 < m := by
          rw [hm]; unfold partialMargin
          have := mul_nonneg hθ.1 (sub_nonneg.2 hq1.le); linarith only [this, hq0]
        have hzb1 : 1 ≤ zb := by
          rw [hzb]; unfold zBar; linarith only [mul_nonneg hθ.1 hL0]
        have hzb0 : 0 < zb := by linarith only [hzb1]
        have hu_neg : ∀ x : ℝ, 0 ≤ x → u P.α P.lam (-x) = -(P.lam * x ^ P.α) := by
          intro x hx; unfold u; split_ifs with h
          · have : x = 0 := by linarith only [h, hx]
            subst this; simp [Real.zero_rpow hα0.ne']
          · rw [neg_neg]
        have hu_pos : ∀ x : ℝ, 0 ≤ x → u P.α P.lam x = x ^ P.α := by
          intro x hx; unfold u; rw [if_pos hx]
        have hu_negv : ∀ x : ℝ, x < 0 → u P.α P.lam x < 0 := by
          intro x hx; unfold u; rw [if_neg (not_le.mpr hx)]
          have : 0 < (-x) ^ P.α := Real.rpow_pos_of_pos (by linarith only [hx]) _
          have := mul_pos (by linarith only [hlam] : (0:ℝ) < P.lam) this; linarith only [this]
        have hpow : ∀ x : ℝ, 0 ≤ x → ((P.z - 1) * x) ^ P.α = P.lam * (1 - P.q) / P.q * x ^ P.α := by
          intro x hx
          rw [Real.mul_rpow hL0 hx, hL, ← Real.rpow_mul hK0, one_div, inv_mul_cancel₀ hα0.ne',
            Real.rpow_one]
        have hbuy : ∀ bb p : ℝ, 0 < bb → 0 ≤ p → buyersP P θ bb p = Set.Icc (bb * p * zb) P.vbar := by
          intro bb p hbb hp
          ext v
          simp only [buyersP, welfareP, Set.mem_ofPred_eq, Set.mem_Icc]
          have hx : 0 ≤ θ * bb * p := mul_nonneg (mul_nonneg hθ.1 hbb.le) hp
          rw [hu_neg _ hx]
          have hzbe : bb * p * zb = bb * p + (P.z - 1) * (θ * bb * p) := by
            rw [hzb]; unfold zBar; ring
          have hzx : 0 ≤ (P.z - 1) * (θ * bb * p) := mul_nonneg hL0 hx
          have hxa : 0 ≤ P.lam * (θ * bb * p) ^ P.α := mul_nonneg (by linarith only [hlam]) (Real.rpow_nonneg hx _)
          have hbp : 0 ≤ bb * p := mul_nonneg hbb.le hp
          constructor
          · rintro ⟨⟨hv0, hv1⟩, hw⟩
            refine ⟨?_, hv1⟩
            by_cases hv : 0 ≤ v - bb * p
            · rw [hu_pos _ hv] at hw
              have key : (P.z - 1) * (θ * bb * p) ≤ v - bb * p := by
                rw [← Real.rpow_le_rpow_iff hzx hv hα0, hpow _ hx]
                rw [div_mul_eq_mul_div, div_le_iff₀ hq0]; linarith only [hw]
              linarith only [key, hzbe]
            · exfalso; push Not at hv
              have h1 := mul_neg_of_pos_of_neg hq0 (hu_negv _ hv)
              have h2 := mul_nonneg (sub_nonneg.2 hq1.le) hxa
              linarith only [h1, h2, hw]
          · rintro ⟨hv0, hv1⟩
            have hv : 0 ≤ v - bb * p := by linarith only [hzbe, hzx, hv0]
            refine ⟨⟨by linarith only [hv, hbp], hv1⟩, ?_⟩
            rw [hu_pos _ hv]
            have key : (P.z - 1) * (θ * bb * p) ≤ v - bb * p := by linarith only [hzbe, hv0]
            rw [← Real.rpow_le_rpow_iff hzx hv hα0, hpow _ hx, div_mul_eq_mul_div, div_le_iff₀ hq0] at key
            linarith only [key]
        have hint : ∀ t A B : ℝ, ∫ v in Set.Icc t P.vbar, (A * v + B) =
            max (P.vbar - t) 0 * (A * (P.vbar + t) / 2 + B) := by
          intro t A B
          rcases le_or_gt t P.vbar with h | h
          · rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h,
              max_eq_left (by linarith only [h])]
            rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun v => A * v ^ 2 / 2 + B * v)]
            · ring
            · intro x _
              have h2 : HasDerivAt (fun v : ℝ => v ^ 2) (2 * x) x := by simpa using hasDerivAt_pow 2 x
              have := ((h2.const_mul A).div_const 2).add ((hasDerivAt_id' x).const_mul B)
              convert this using 1
              · funext v; simp only [Pi.add_apply]
              · ring
            · exact ((continuous_const.mul continuous_id).add continuous_const).intervalIntegrable _ _
          · rw [Set.Icc_eq_empty (by linarith only [h]), max_eq_right (by linarith only [h]),
              MeasureTheory.Measure.restrict_empty, MeasureTheory.integral_zero_measure, zero_mul]
        have hdem : ∀ bb p : ℝ, 0 < bb → 0 ≤ p →
            demandP P θ bb p = P.n / P.vbar * max (P.vbar - bb * p * zb) 0 := by
          intro bb p hbb hp
          unfold demandP; rw [hbuy bb p hbb hp, Real.volume_Icc, ENNReal.toReal_ofReal']
        have hpat : ∀ bb p : ℝ, 0 < bb → 0 ≤ p → patientPayoffP P θ bb p =
            P.n / P.vbar * (max (P.vbar - bb * p * zb) 0 * (P.q * (P.vbar + bb * p * zb) / 2 - m * bb * p)) := by
          intro bb p hbb hp
          unfold patientPayoffP; rw [hbuy bb p hbb hp]
          have : ∀ v : ℝ, P.q * (v - bb * p) - (1 - P.q) * θ * bb * p = P.q * v + (-(m * bb * p)) := by
            intro v; rw [hm]; unfold partialMargin; ring
          simp_rw [this]
          rw [hint]; ring
        have hobj : ∀ bb p : ℝ, 0 < bb → 0 ≤ p → payerObjP P θ bb p =
            P.n / P.vbar * (max (P.vbar - bb * p * zb) 0 *
              (P.q * P.vp - m * p + P.q * (P.vbar + bb * p * zb) / 2)) := by
          intro bb p hbb hp
          unfold payerObjP payerPayoffP; rw [hdem bb p hbb hp, hpat bb p hbb hp, hm]
          unfold partialMargin; ring
        have hfirm : ∀ bb p : ℝ, 0 < bb → 0 ≤ p → firmProfitP P θ bb p =
            (m * p - P.c) * (P.n / P.vbar * max (P.vbar - bb * p * zb) 0) := by
          intro bb p hbb hp
          unfold firmProfitP; rw [hdem bb p hbb hp, hm]
        have hk : 0 < P.n / P.vbar := div_pos hn hvbar
        set r := P.c / m with hr_def
        set s := P.vbar / zb with hs_def
        set w := P.vbar / (P.β * zb) with hw_def
        have hβzb : 0 < P.β * zb := mul_pos hβ0 hzb0
        have hcr : P.c = m * r := (mul_div_cancel₀ P.c hm_pos.ne').symm
        have hvs : P.vbar = zb * s := (mul_div_cancel₀ P.vbar hzb0.ne').symm
        have hvw : P.vbar = P.β * zb * w := (mul_div_cancel₀ P.vbar hβzb.ne').symm
        have hsw : s = P.β * w := mul_left_cancel₀ hzb0.ne' (by rw [← hvs]; rw [hvw]; ring)
        have hr0 : 0 < r := div_pos hc hm_pos
        have hs0 : 0 < s := div_pos hvbar hzb0
        have hw0 : 0 < w := div_pos hvbar hβzb
        clear_value r s w
        have hs2 : 2 * s ≤ w := by
          rw [hsw]; have := mul_le_mul_of_nonneg_right hβ1 hw0.le; linarith only [this]
        have hsw' : s < w := by linarith only [hs2, hs0]
        have hrw : r < w := by
          have h := hA
          unfold PartialAssumption at h
          rw [← hm, ← hzb] at h
          rw [div_lt_div_iff₀ hvbar hzb0] at h
          have e1 : P.β * P.c * zb = (m * P.β * zb) * r := by rw [hcr]; ring
          have e2 : m * P.vbar = (m * P.β * zb) * w := by rw [hvw]; ring
          rw [e1, e2] at h
          exact lt_of_mul_lt_mul_left h (mul_pos (mul_pos hm_pos hβ0) hzb0).le
        obtain ⟨C, hC_def⟩ : ∃ C, C = P.n / P.vbar * m * zb := ⟨_, rfl⟩
        have hC : 0 < C := by rw [hC_def]; exact mul_pos (mul_pos hk hm_pos) hzb0
        obtain ⟨Fb, hFb_def⟩ : ∃ f : ℝ → ℝ, ∀ p, f p = P.β * (p - r) * max (w - p) 0 :=
          ⟨_, fun _ => rfl⟩
        obtain ⟨F1, hF1_def⟩ : ∃ f : ℝ → ℝ, ∀ p, f p = (p - r) * max (s - p) 0 :=
          ⟨_, fun _ => rfl⟩
        have e2 : ∀ p, max (P.vbar - P.β * p * zb) 0 = P.β * zb * max (w - p) 0 := by
          intro p
          rw [show P.vbar - P.β * p * zb = (P.β * zb) * (w - p) by rw [hvw]; ring,
            mul_max_of_nonneg _ _ hβzb.le, mul_zero]
        have e1 : ∀ p, max (P.vbar - 1 * p * zb) 0 = zb * max (s - p) 0 := by
          intro p
          rw [show P.vbar - 1 * p * zb = zb * (s - p) by rw [hvs]; ring,
            mul_max_of_nonneg _ _ hzb0.le, mul_zero]
        have hFbfirm : ∀ p, 0 ≤ p → firmProfitP P θ P.β p = C * Fb p := by
          intro p hp
          rw [hfirm _ _ hβ0 hp, e2, hFb_def, hcr, hC_def]; ring
        have hF1firm : ∀ p, 0 ≤ p → firmProfitP P θ 1 p = C * F1 p := by
          intro p hp
          rw [hfirm _ _ one_pos hp, e1, hF1_def, hcr, hC_def]; ring
        have hcov : ∀ p, 0 ≤ p → (coversP P θ p ↔
            zb * max (s - p) 0 * (P.q * P.vp - m * p + P.q * (P.vbar + 1 * p * zb) / 2) ≤
            P.β * zb * max (w - p) 0 * (P.q * P.vp - m * p + P.q * (P.vbar + P.β * p * zb) / 2)) := by
          intro p hp
          unfold coversP
          rw [hobj 1 p one_pos hp, hobj P.β p hβ0 hp, e1, e2]
          exact ⟨fun h => le_of_mul_le_mul_left h hk, fun h => mul_le_mul_of_nonneg_left h hk.le⟩
        have hreg1 : ∀ p, 0 ≤ p → p ≤ s → (coversP P θ p ↔ p * b ≤ P.q * P.vp) := by
          intro p hp hps
          rw [hcov p hp, max_eq_left (by linarith only [hps]), max_eq_left (by linarith only [hps, hsw'] : (0:ℝ) ≤ w - p)]
          have key : P.β * zb * (w - p) * (P.q * P.vp - m * p + P.q * (P.vbar + P.β * p * zb) / 2) -
              zb * (s - p) * (P.q * P.vp - m * p + P.q * (P.vbar + 1 * p * zb) / 2) =
              (1 - P.β) * p * zb * (P.q * P.vp - p * b) := by
            rw [hb, hvs, hsw]; ring
          constructor
          · intro h
            rcases hp.lt_or_eq with hp' | hp'
            · by_contra hcon
              push Not at hcon
              have : (1 - P.β) * p * zb * (P.q * P.vp - p * b) < 0 :=
                mul_neg_of_pos_of_neg (mul_pos (mul_pos (by linarith only [hβ1]) hp') hzb0) (by linarith only [hcon])
              linarith only [this, key, h]
            · rw [← hp', zero_mul]; exact mul_nonneg hq0.le hvp
          · intro h
            have : 0 ≤ (1 - P.β) * p * zb * (P.q * P.vp - p * b) :=
              mul_nonneg (mul_nonneg (mul_nonneg (by linarith only [hβ1]) hp) hzb0.le) (by linarith only [h])
            linarith only [this, key]
        have hreg2 : ∀ p, s ≤ p → p < w → (coversP P θ p ↔ p * a ≤ P.q * (P.vp + P.vbar / 2)) := by
          intro p hsp hpw
          have hp : 0 ≤ p := by linarith only [hsp, hs0]
          rw [hcov p hp, max_eq_right (by linarith only [hsp]), max_eq_left (by linarith only [hpw] : (0:ℝ) ≤ w - p),
            mul_zero, zero_mul,
            show P.q * P.vp - m * p + P.q * (P.vbar + P.β * p * zb) / 2 =
              P.q * (P.vp + P.vbar / 2) - p * a by rw [ha]; ring,
            mul_nonneg_iff_of_pos_left (mul_pos hβzb (by linarith only [hpw])), sub_nonneg]
        have hreg3 : ∀ p, w ≤ p → coversP P θ p := by
          intro p hp
          rw [hcov p (by linarith only [hp, hw0]), max_eq_right (by linarith only [hp, hsw']),
            max_eq_right (by linarith only [hp]), mul_zero, zero_mul, mul_zero, zero_mul]
        have hRc : ∀ p, 0 ≤ p → coversP P θ p → realizedProfitP P θ p = C * Fb p := by
          intro p hp h; unfold realizedProfitP shareP; rw [if_pos h, hFbfirm p hp]
        have hRn : ∀ p, 0 ≤ p → ¬coversP P θ p → realizedProfitP P θ p = C * F1 p := by
          intro p hp h; unfold realizedProfitP shareP; rw [if_neg h, hF1firm p hp]
        have hFb_eq : ∀ p, p ≤ w → Fb p = P.β * (p - r) * (w - p) := by
          intro p hp; rw [hFb_def, max_eq_left (by linarith only [hp])]
        have hFb_zero : ∀ p, w ≤ p → Fb p = 0 := by
          intro p hp; rw [hFb_def, max_eq_right (by linarith only [hp]), mul_zero]
        have hF1_eq : ∀ p, p ≤ s → F1 p = (p - r) * (s - p) := by
          intro p hp; rw [hF1_def, max_eq_left (by linarith only [hp])]
        have hF1_zero : ∀ p, s ≤ p → F1 p = 0 := by
          intro p hp; rw [hF1_def, max_eq_right (by linarith only [hp]), mul_zero]
        have hle1 : ∀ p, 0 ≤ p → F1 p ≤ max (Fb p) 0 := by
          intro p hp
          rcases le_or_gt p s with h | h
          · rw [hF1_eq p h, hFb_eq p (by linarith only [h, hsw'])]
            by_cases hpr : r ≤ p
            · apply le_max_of_le_left
              have e : P.β * (p - r) * (w - p) - (p - r) * (s - p) = (p - r) * p * (1 - P.β) := by
                rw [hsw]; ring
              have := mul_nonneg (mul_nonneg (sub_nonneg.2 hpr) hp) (by linarith only [hβ1] : (0:ℝ) ≤ 1 - P.β)
              linarith only [e, this]
            · apply le_max_of_le_right
              push Not at hpr
              have := mul_nonneg (sub_nonneg.2 hpr.le) (sub_nonneg.2 h)
              have e : (p - r) * (s - p) = -((r - p) * (s - p)) := by ring
              linarith only [e, this]
          · rw [hF1_zero p h.le]; exact le_max_right _ _
        have hFb_le : ∀ p, Fb p ≤ Fb ((r + w) / 2) := by
          intro p
          rw [hFb_eq ((r + w) / 2) (by linarith only [hrw])]
          rcases le_or_gt p w with h | h
          · rw [hFb_eq p h]
            have e : P.β * ((r + w) / 2 - r) * (w - (r + w) / 2) - P.β * (p - r) * (w - p) =
              P.β * (p - (r + w) / 2) ^ 2 := by ring
            linarith only [e, mul_nonneg hβ0.le (sq_nonneg (p - (r + w) / 2))]
          · rw [hFb_zero p h.le]
            have e : P.β * ((r + w) / 2 - r) * (w - (r + w) / 2) = P.β * (w - r) ^ 2 / 4 := by ring
            linarith only [e, mul_nonneg hβ0.le (sq_nonneg (w - r))]
        have hFb_pos : 0 < Fb ((r + w) / 2) := by
          rw [hFb_eq ((r + w) / 2) (by linarith only [hrw])]
          have h1 : 0 < (r + w) / 2 - r := by linarith only [hrw]
          have h2 : 0 < w - (r + w) / 2 := by linarith only [hrw]
          exact mul_pos (mul_pos hβ0 h1) h2
        have hFb_mono : ∀ x y, x ≤ y → y ≤ w → x + y ≤ r + w → Fb x ≤ Fb y := by
          intro x y hxy hyw hs
          rw [hFb_eq x (by linarith only [hxy, hyw]), hFb_eq y hyw]
          have e : P.β * (y - r) * (w - y) - P.β * (x - r) * (w - x) = P.β * (y - x) * (r + w - x - y) := by ring
          linarith only [e, mul_nonneg (mul_nonneg hβ0.le (sub_nonneg.2 hxy)) (by linarith only [hs] : (0:ℝ) ≤ r + w - x - y)]
        have hFb_smono : ∀ x y, x < y → y ≤ w → x + y < r + w → Fb x < Fb y := by
          intro x y hxy hyw hs
          rw [hFb_eq x (by linarith only [hxy, hyw]), hFb_eq y hyw]
          have e : P.β * (y - r) * (w - y) - P.β * (x - r) * (w - x) = P.β * (y - x) * (r + w - x - y) := by ring
          linarith only [e, mul_pos (mul_pos hβ0 (sub_pos.2 hxy)) (by linarith only [hs] : (0:ℝ) < r + w - x - y)]
        have hF1_le : r ≤ s → ∀ p, F1 p ≤ F1 ((r + s) / 2) := by
          intro hrs p
          rw [hF1_eq ((r + s) / 2) (by linarith only [hrs])]
          rcases le_or_gt p s with h | h
          · rw [hF1_eq p h]
            have e : ((r + s) / 2 - r) * (s - (r + s) / 2) - (p - r) * (s - p) = (p - (r + s) / 2) ^ 2 := by ring
            linarith only [e, sq_nonneg (p - (r + s) / 2)]
          · rw [hF1_zero p h.le]
            have e : ((r + s) / 2 - r) * (s - (r + s) / 2) = (s - r) ^ 2 / 4 := by ring
            linarith only [e, sq_nonneg (s - r)]
        have hF1_nonneg : r ≤ s → 0 ≤ F1 ((r + s) / 2) := by
          intro hrs
          rw [hF1_eq ((r + s) / 2) (by linarith only [hrs])]
          exact mul_nonneg (by linarith only [hrs]) (by linarith only [hrs])
        have hF1_pos : r < s → 0 < F1 ((r + s) / 2) := by
          intro hrs
          rw [hF1_eq ((r + s) / 2) (by linarith only [hrs])]
          exact mul_pos (by linarith only [hrs]) (by linarith only [hrs])
        have hF1_peak : r ≤ s → ∀ p, p ≤ s → F1 ((r + s) / 2) ≤ F1 p → p = (r + s) / 2 := by
          intro hrs p hp h
          rw [hF1_eq p hp, hF1_eq _ (by linarith only [hrs])] at h
          have e : ((r + s) / 2 - r) * (s - (r + s) / 2) - (p - r) * (s - p) = (p - (r + s) / 2) ^ 2 := by ring
          have h0 : (p - (r + s) / 2) ^ 2 = 0 := le_antisymm (by linarith only [e, h]) (sq_nonneg _)
          have := (pow_eq_zero_iff two_ne_zero).1 h0
          linarith only [this]
        have hFb_peak : ∀ p, Fb ((r + w) / 2) ≤ Fb p → p = (r + w) / 2 := by
          intro p h
          rcases le_or_gt p w with hpw | hpw
          · have h' := h
            rw [hFb_eq p hpw, hFb_eq _ (by linarith only [hrw])] at h'
            by_contra hne
            have : 0 < (p - (r + w) / 2) ^ 2 := by
              have : p - (r + w) / 2 ≠ 0 := sub_ne_zero.2 hne
              positivity
            have e : P.β * ((r + w) / 2 - r) * (w - (r + w) / 2) - P.β * (p - r) * (w - p) =
              P.β * (p - (r + w) / 2) ^ 2 := by ring
            linarith only [e, h', mul_pos hβ0 this]
          · rw [hFb_zero p hpw.le] at h; linarith only [h, hFb_pos]
        have hF1_lt : ∀ p, 0 < p → 0 < F1 p → F1 p < Fb p := by
          intro p hp h
          rcases le_or_gt s p with hsp | hsp
          · rw [hF1_zero p hsp] at h; exact absurd h (lt_irrefl 0)
          · rw [hF1_eq p hsp.le] at h ⊢
            rw [hFb_eq p (by linarith only [hsp, hsw'])]
            have hpr : 0 < p - r := by
              by_contra hh; push Not at hh
              have := mul_nonneg (by linarith only [hh] : (0:ℝ) ≤ r - p) (by linarith only [hsp] : (0:ℝ) ≤ s - p)
              have e : (p - r) * (s - p) = -((r - p) * (s - p)) := by ring
              linarith only [this, e, h]
            have e : P.β * (p - r) * (w - p) - (p - r) * (s - p) = (p - r) * p * (1 - P.β) := by
              rw [hsw]; ring
            linarith only [e, mul_pos (mul_pos hpr hp) (by linarith only [hβ1] : (0:ℝ) < 1 - P.β)]
        have hR_le : ∀ p, 0 ≤ p → realizedProfitP P θ p ≤ C * max (Fb p) 0 := by
          intro p hp
          by_cases h : coversP P θ p
          · rw [hRc p hp h]; exact mul_le_mul_of_nonneg_left (le_max_left _ _) hC.le
          · rw [hRn p hp h]; exact mul_le_mul_of_nonneg_left (hle1 p hp) hC.le
        have hps : pPartialStar P θ = (r + w) / 2 := by
          unfold pPartialStar; rw [← hm, ← hzb, hr_def, hw_def]; ring
        have hpbs : pPartialBarStar P θ = (r + s) / 2 := by
          unfold pPartialBarStar; rw [← hm, ← hzb, hr_def, hs_def]; ring
        have hroot : ∀ p3, rootP p3 ↔ (r ≤ p3 ∧ p3 ≤ (r + s) / 2) ∧ F1 ((r + s) / 2) = Fb p3 := by
          intro p3
          rw [hrootdef, hpbs, Set.mem_Icc, hF1firm _ (by linarith only [hr0, hs0])]
          constructor
          · rintro ⟨⟨h1, h2⟩, h3⟩
            rw [hFbfirm p3 (by linarith only [h1, hr0])] at h3
            exact ⟨⟨h1, h2⟩, mul_left_cancel₀ hC.ne' h3⟩
          · rintro ⟨⟨h1, h2⟩, h3⟩
            rw [hFbfirm p3 (by linarith only [h1, hr0]), h3]; exact ⟨⟨h1, h2⟩, rfl⟩
        clear hbuy hint hdem hpat hobj hfirm hu_neg hu_pos hu_negv hpow hL hK0 hcov e1 e2 hFbfirm hF1firm hrootdef hA hm hzb hs_def hw_def hC_def hL0 hzb1 hcr hvw hβzb
        rw [hps, hpbs]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · -- part 1
          intro hrs
          have hcont : ContinuousOn (fun p => P.β * (p - r) * (w - p)) (Set.Icc r ((r + s) / 2)) :=
            ((continuous_const.mul (continuous_id.sub continuous_const)).mul
              (continuous_const.sub continuous_id)).continuousOn
          have hmem : F1 ((r + s) / 2) ∈ Set.Icc ((fun p => P.β * (p - r) * (w - p)) r)
              ((fun p => P.β * (p - r) * (w - p)) ((r + s) / 2)) := by
            have h0 := hF1_nonneg hrs
            rw [hF1_eq _ (by linarith only [hrs])] at h0 ⊢
            refine ⟨by simp only [sub_self, mul_zero, zero_mul]; exact h0, ?_⟩
            show _ ≤ P.β * ((r + s) / 2 - r) * (w - (r + s) / 2)
            have e : P.β * ((r + s) / 2 - r) * (w - (r + s) / 2) - ((r + s) / 2 - r) * (s - (r + s) / 2) =
              ((r + s) / 2 - r) * ((r + s) / 2) * (1 - P.β) := by rw [hsw]; ring
            have := mul_nonneg (mul_nonneg (by linarith only [hrs] : (0:ℝ) ≤ (r + s) / 2 - r)
              (by linarith only [hr0, hs0] : (0:ℝ) ≤ (r + s) / 2)) (by linarith only [hβ1] : (0:ℝ) ≤ 1 - P.β)
            linarith only [e, this]
          obtain ⟨p3, ⟨h1, h2⟩, h3⟩ := intermediate_value_Icc (by linarith only [hrs]) hcont hmem
          have h3' : F1 ((r + s) / 2) = Fb p3 := by
            rw [hFb_eq p3 (by linarith only [h2, hrs, hsw'])]; exact h3.symm
          refine ⟨p3, (hroot p3).2 ⟨⟨h1, h2⟩, h3'⟩, ?_⟩
          intro y hy
          obtain ⟨⟨hy1, hy2⟩, hy3⟩ := (hroot y).1 hy
          by_contra hne
          rcases lt_or_gt_of_ne hne with h | h
          · have := hFb_smono y p3 h (by linarith only [h2, hrs, hsw']) (by linarith only [h2, hy2, hsw'])
            linarith only [this, h3', hy3]
          · have := hFb_smono p3 y h (by linarith only [hy2, hrs, hsw']) (by linarith only [h2, hy2, hsw'])
            linarith only [this, h3', hy3]
        · -- part 2
          intro hcond
          have hsps : s ≤ (r + w) / 2 := by linarith only [hs2, hr0]
          have hpsw : (r + w) / 2 < w := by linarith only [hrw]
          have hps0 : 0 ≤ (r + w) / 2 := by linarith only [hr0, hw0]
          have hcv : coversP P θ ((r + w) / 2) := by
            rw [hreg2 _ hsps hpsw]
            rcases hcond with h | h
            · have ha0 : a ≤ 0 := by rw [ha]; linarith only [h]
              have := mul_nonpos_of_nonneg_of_nonpos hps0 ha0
              have := mul_nonneg hq0.le (by linarith only [hvp, hvbar] : (0:ℝ) ≤ P.vp + P.vbar / 2)
              linarith only [this, ‹(r + w) / 2 * a ≤ 0›]
            · have h' : (r + w) / 2 * a / P.q ≤ P.vp + P.vbar / 2 := by linarith only [h]
              rw [div_le_iff₀ hq0] at h'; linarith only [h']
          have hRps := hRc _ hps0 hcv
          refine ⟨⟨hps0, fun p hp => ?_⟩, hcv, ?_⟩
          · rw [hRps]
            exact (hR_le p hp).trans (mul_le_mul_of_nonneg_left (max_le (hFb_le p) hFb_pos.le) hC.le)
          · rintro p ⟨hp, hmax⟩
            have h := hmax _ hps0
            rw [hRps] at h
            by_cases hc' : coversP P θ p
            · rw [hRc p hp hc'] at h
              exact hFb_peak p (le_of_mul_le_mul_left h hC)
            · rw [hRn p hp hc'] at h
              have h1 : Fb ((r + w) / 2) ≤ F1 p := le_of_mul_le_mul_left h hC
              have hpp : 0 < p := by
                rcases hp.lt_or_eq with h' | h'
                · exact h'
                · rw [← h', hF1_eq 0 hs0.le] at h1
                  have := mul_neg_of_neg_of_pos (by linarith only [hr0] : (0:ℝ) - r < 0) (by linarith only [hs0] : (0:ℝ) < s - 0)
                  linarith only [this, h1, hFb_pos]
              have := hF1_lt p hpp (by linarith only [h1, hFb_pos])
              linarith only [this, hFb_le p, h1]
        · -- part 3
          rintro ⟨h1, h2, h3⟩
          have ha0 : 0 < a := by rw [ha]; linarith only [h1]
          have hp1a : p1 * a = P.q * (P.vp + P.vbar / 2) := by rw [hp1]; exact div_mul_cancel₀ _ ha0.ne'
          have hmx : max r s < p1 := by
            have : max r s * a / P.q < P.vp + P.vbar / 2 := by linarith only [h2]
            rw [div_lt_iff₀ hq0] at this
            exact lt_of_mul_lt_mul_right (by linarith only [this, hp1a]) ha0.le
          have hrp1 : r < p1 := lt_of_le_of_lt (le_max_left _ _) hmx
          have hsp1 : s < p1 := lt_of_le_of_lt (le_max_right _ _) hmx
          have hp1ps : p1 < (r + w) / 2 := by
            have : P.vp + P.vbar / 2 < (r + w) / 2 * a / P.q := by linarith only [h3]
            rw [lt_div_iff₀ hq0] at this
            exact lt_of_mul_lt_mul_right (by linarith only [this, hp1a]) ha0.le
          have hp10 : 0 ≤ p1 := by linarith only [hrp1, hr0]
          have hp1w : p1 < w := by linarith only [hp1ps, hrw]
          have hcv : coversP P θ p1 := (hreg2 p1 hsp1.le hp1w).2 (le_of_eq hp1a)
          have hRp1 := hRc p1 hp10 hcv
          have hFbp1 : 0 < Fb p1 := by
            rw [hFb_eq p1 hp1w.le]; exact mul_pos (mul_pos hβ0 (by linarith only [hrp1])) (by linarith only [hp1w])
          have hhigh : ∀ p, 0 ≤ p → p1 < p → realizedProfitP P θ p ≤ 0 := by
            intro p hp hpp
            rcases lt_or_ge p w with hpw | hpw
            · have hnc : ¬coversP P θ p := by
                intro hc'
                have := (hreg2 p (by linarith only [hsp1, hpp]) hpw).1 hc'
                have := mul_lt_mul_of_pos_right hpp ha0
                linarith only [this, hp1a, ‹p * a ≤ P.q * (P.vp + P.vbar / 2)›]
              rw [hRn p hp hnc, hF1_zero p (by linarith only [hsp1, hpp]), mul_zero]
            · rw [hRc p hp (hreg3 p hpw), hFb_zero p hpw, mul_zero]
          have hlow : ∀ p, 0 ≤ p → p < p1 → realizedProfitP P θ p < C * Fb p1 := by
            intro p hp hpp
            exact lt_of_le_of_lt (hR_le p hp) (mul_lt_mul_of_pos_left (max_lt
              (hFb_smono p p1 hpp hp1w.le (by linarith only [hpp, hp1ps])) hFbp1) hC)
          refine ⟨⟨hp10, fun p hp => ?_⟩, hcv, ?_⟩
          · rw [hRp1]
            rcases lt_trichotomy p p1 with h | h | h
            · exact (hlow p hp h).le
            · rw [h, hRp1]
            · linarith only [hhigh p hp h, mul_pos hC hFbp1]
          · rintro p ⟨hp, hmax⟩
            have h := hmax p1 hp10
            rw [hRp1] at h
            rcases lt_trichotomy p p1 with h' | h' | h'
            · linarith only [hlow p hp h', h]
            · exact h'
            · linarith only [hhigh p hp h', mul_pos hC hFbp1, h]
        · intro p3 hp3
          obtain ⟨⟨h31, h32⟩, h33⟩ := (hroot p3).1 hp3
          have hp30 : 0 ≤ p3 := by linarith only [h31, hr0]
          have hab : a = b + P.q * zb / 2 := by rw [ha, hb]; ring
          have hqz : 0 < P.q * zb / 2 := div_pos (mul_pos hq0 hzb0) two_pos
          constructor
          · rintro ⟨hrs, hbm, h4, h5⟩
            have hb0 : 0 < b := by rw [hb]; linarith only [hbm]
            have ha0 : 0 < a := by rw [hab]; linarith only [hb0, hqz]
            have h4' := (div_le_iff₀ hq0).1 h4
            have hp2b : p2 * b = P.q * P.vp := by rw [hp2]; exact div_mul_cancel₀ _ hb0.ne'
            have hp32 : p3 ≤ p2 := le_of_mul_le_mul_right (by linarith only [h4', hp2b]) hb0
            have h5' : (P.vp + P.vbar / 2) * P.q ≤ s * a := by
              have : P.vp + P.vbar / 2 ≤ s * a / P.q := by linarith only [h5]
              rwa [le_div_iff₀ hq0] at this
            have e : s * a = s * b + P.q * P.vbar / 2 := by rw [hab, hvs]; ring
            have hp2s : p2 ≤ s := le_of_mul_le_mul_right (by linarith only [hp2b, h5', e]) hb0
            have hp20 : 0 ≤ p2 := by rw [hp2]; exact div_nonneg (mul_nonneg hq0.le hvp) hb0.le
            have hcv : coversP P θ p2 := (hreg1 p2 hp20 hp2s).2 (le_of_eq hp2b)
            have hRp2 := hRc p2 hp20 hcv
            have hFb32 : Fb p3 ≤ Fb p2 :=
              hFb_mono p3 p2 hp32 (by linarith only [hp2s, hsw']) (by linarith only [h32, hp2s, hs2, hr0, hw0])
            have hF1n := hF1_nonneg hrs
            have habove : ∀ p, 0 ≤ p → p2 < p → realizedProfitP P θ p ≤ C * Fb p3 := by
              intro p hp hpp
              rcases le_or_gt p s with hps' | hps'
              · have hnc : ¬coversP P θ p := fun hc' => by
                  have i1 := (hreg1 p hp hps').1 hc'
                  have i2 := mul_lt_mul_of_pos_right hpp hb0
                  linarith only [i1, i2, hp2b]
                rw [hRn p hp hnc, ← h33]; exact mul_le_mul_of_nonneg_left (hF1_le hrs p) hC.le
              · rcases lt_or_ge p w with hpw | hpw
                · have hnc : ¬coversP P θ p := fun hc' => by
                    have i1 := (hreg2 p hps'.le hpw).1 hc'
                    have i2 := mul_lt_mul_of_pos_right hps' ha0
                    linarith only [i1, i2, h5']
                  rw [hRn p hp hnc, hF1_zero p hps'.le, mul_zero, ← h33]; exact mul_nonneg hC.le hF1n
                · rw [hRc p hp (hreg3 p hpw), hFb_zero p hpw, mul_zero, ← h33]; exact mul_nonneg hC.le hF1n
            refine ⟨⟨hp20, fun p hp => ?_⟩, hcv, ?_⟩
            · rw [hRp2]
              rcases le_or_gt p p2 with h | h
              · exact (hR_le p hp).trans (mul_le_mul_of_nonneg_left (max_le
                  (hFb_mono p p2 h (by linarith only [hp2s, hsw']) (by linarith only [h, hp2s, hs2, hr0]))
                  (by linarith only [hFb32, hF1n, h33])) hC.le)
              · exact (habove p hp h).trans (mul_le_mul_of_nonneg_left hFb32 hC.le)
            · intro hlt p ⟨hp, hmax⟩
              have hlt' : p3 < p2 := by
                have := (div_lt_iff₀ hq0).1 hlt
                exact lt_of_mul_lt_mul_right (by linarith only [this, hp2b]) hb0.le
              have hFs : Fb p3 < Fb p2 :=
                hFb_smono p3 p2 hlt' (by linarith only [hp2s, hsw']) (by linarith only [h32, hp2s, hs2, hr0, hw0])
              have h := hmax p2 hp20
              rw [hRp2] at h
              rcases lt_trichotomy p p2 with h' | h' | h'
              · exfalso
                have i1 := hFb_smono p p2 h' (by linarith only [hp2s, hsw']) (by linarith only [h', hp2s, hs2, hr0])
                have := lt_of_le_of_lt (hR_le p hp) (mul_lt_mul_of_pos_left
                  (max_lt i1 (by linarith only [hFs, hF1n, h33])) hC)
                linarith only [this, h]
              · exact h'
              · have i1 := habove p hp h'
                have i2 := mul_lt_mul_of_pos_left hFs hC
                linarith only [i1, i2, h]
          · rintro ⟨hrs, hbm, h4⟩
            have hb0 : 0 < b := by rw [hb]; linarith only [hbm]
            have h4' := (lt_div_iff₀ hq0).1 h4
            have hpbs_s : (r + s) / 2 ≤ s := by linarith only [hrs]
            have hpb0 : 0 ≤ (r + s) / 2 := by linarith only [hr0, hs0]
            have hF1n := hF1_nonneg hrs
            have hmid : ∀ p, p3 ≤ p → p ≤ s → ¬coversP P θ p := fun p h1 h2 hc' => by
              have i1 := (hreg1 p (by linarith only [h1, hp30]) h2).1 hc'
              have i2 := mul_le_mul_of_nonneg_right h1 hb0.le
              linarith only [i1, i2, h4']
            have hhigh : ∀ p, s < p → p < w → ¬coversP P θ p := fun p h1 h2 hc' => by
              have i0 := (hreg2 p h1.le h2).1 hc'
              have e : p * a = p * b + p * (P.q * zb / 2) := by rw [hab]; ring
              have i1 := mul_le_mul_of_nonneg_right (by linarith only [h1, h32, hpbs_s] : p3 ≤ p) hb0.le
              have i2 := mul_lt_mul_of_pos_right h1 hqz
              have e2 : s * (P.q * zb / 2) = P.q * (P.vbar / 2) := by rw [hvs]; ring
              linarith only [e, i1, i2, e2, i0, h4']
            have hnc : ¬coversP P θ ((r + s) / 2) := hmid _ h32 hpbs_s
            have hRpb := hRn _ hpb0 hnc
            refine ⟨⟨hpb0, fun p hp => ?_⟩, hnc, ?_⟩
            · rw [hRpb]
              rcases lt_or_ge p p3 with h | h
              · exact (hR_le p hp).trans (mul_le_mul_of_nonneg_left (max_le (le_trans
                  (hFb_mono p p3 h.le (by linarith only [h32, hrs, hsw']) (by linarith only [h, h32, hsw', hrs]))
                  (le_of_eq h33.symm)) hF1n) hC.le)
              · rcases le_or_gt p s with h' | h'
                · rw [hRn p hp (hmid p h h')]; exact mul_le_mul_of_nonneg_left (hF1_le hrs p) hC.le
                · rcases lt_or_ge p w with h'' | h''
                  · rw [hRn p hp (hhigh p h' h''), hF1_zero p h'.le, mul_zero]; exact mul_nonneg hC.le hF1n
                  · rw [hRc p hp (hreg3 p h''), hFb_zero p h'', mul_zero]; exact mul_nonneg hC.le hF1n
            · intro hrs' p ⟨hp, hmax⟩
              have h := hmax _ hpb0
              rw [hRpb] at h
              have hpos := hF1_pos hrs'
              rcases lt_or_ge p p3 with h1 | h1
              · exfalso
                have i1 := hFb_smono p p3 h1 (by linarith only [h32, hrs, hsw']) (by linarith only [h1, h32, hsw', hrs])
                have := lt_of_le_of_lt (hR_le p hp) (mul_lt_mul_of_pos_left
                  (max_lt i1 (by linarith only [hpos, h33])) hC)
                rw [h33] at h; linarith only [this, h]
              · rcases le_or_gt p s with h2 | h2
                · rw [hRn p hp (hmid p h1 h2)] at h
                  exact hF1_peak hrs p h2 (le_of_mul_le_mul_left h hC)
                · exfalso
                  rcases lt_or_ge p w with h3 | h3
                  · rw [hRn p hp (hhigh p h2 h3), hF1_zero p h2.le, mul_zero] at h
                    linarith only [h, mul_pos hC hpos]
                  · rw [hRc p hp (hreg3 p h3), hFb_zero p h3, mul_zero] at h
                    linarith only [h, mul_pos hC hpos]
        · rintro ⟨h1, h2, h3⟩
          have ha0 : 0 < a := by rw [ha]; linarith only [h2]
          have e : P.c / P.q * a / m = r * a / P.q := by rw [hr_def]; ring
          rw [e] at h3 ⊢
          have h3' : (P.vp + P.vbar / 2) * P.q ≤ r * a := by
            have : P.vp + P.vbar / 2 ≤ r * a / P.q := by linarith only [h3]
            rwa [le_div_iff₀ hq0] at this
          have hnc : ∀ p, r < p → p < w → ¬coversP P θ p := fun p hp hpw hc' => by
            have i1 := (hreg2 p (by linarith only [h1, hp]) hpw).1 hc'
            have i2 := mul_lt_mul_of_pos_right hp ha0
            linarith only [i1, i2, h3']
          refine ⟨fun p hp => ?_, ⟨r, hr0.le, ?_⟩, hnc, ?_⟩
          · rcases le_or_gt p r with hpr | hpr
            · by_cases hc' : coversP P θ p
              · rw [hRc p hp hc', hFb_def]
                exact mul_nonpos_of_nonneg_of_nonpos hC.le (mul_nonpos_of_nonpos_of_nonneg
                  (mul_nonpos_of_nonneg_of_nonpos hβ0.le (by linarith only [hpr])) (le_max_right _ _))
              · rw [hRn p hp hc', hF1_def]
                exact mul_nonpos_of_nonneg_of_nonpos hC.le (mul_nonpos_of_nonpos_of_nonneg
                  (by linarith only [hpr]) (le_max_right _ _))
            · rcases lt_or_ge p w with hpw | hpw
              · rw [hRn p hp (hnc p hpr hpw), hF1_zero p (by linarith only [h1, hpr]), mul_zero]
              · rw [hRc p hp (hreg3 p hpw), hFb_zero p hpw, mul_zero]
          · by_cases hc' : coversP P θ r
            · rw [hRc r hr0.le hc', hFb_def, sub_self, mul_zero, zero_mul, mul_zero]
            · rw [hRn r hr0.le hc', hF1_def, sub_self, zero_mul, mul_zero]
          · intro hlt hc'
            have h3'' : (P.vp + P.vbar / 2) * P.q < r * a := by
              have : P.vp + P.vbar / 2 < r * a / P.q := by linarith only [hlt]
              rwa [lt_div_iff₀ hq0] at this
            have := (hreg2 r h1.le hrw).1 hc'
            linarith only [this, h3'']
