-- Prove2me | solution 1 for OutcomeRebate.Transfer.Supplement.theorem_2
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:04:48.103897+00:00
-- url     : https://prove2.me/submissions/7209cfb0-72b5-469e-9a7d-7461071c93e1

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model
import Definitions.Def_OutcomeRebate_Transfer_Supplement_OutcomePrices

open OutcomeRebate
open OutcomeRebate.Transfer
open OutcomeRebate.Transfer.Supplement

theorem solution (P : Params) (hS : P.Standing) (hA : Assumption1 P) :
    let rootP := fun p3 : ℝ => p3 ∈ Set.Icc (P.c / P.q) (pHatStar P) ∧
      firmProfitO P 1 (pHatStar P) = firmProfitO P P.β p3
    let a := 1 - P.β / 2
    let b := (1 - P.β) / 2
    let p1 := (P.vp + P.vbar / 2) / a
    let p2 := 2 * P.vp / (1 - P.β)
    let C1 := pTilde P * a - P.vbar / 2 ≤ P.vp
    let C2 := max (P.c / P.q) P.vbar * a - P.vbar / 2 < P.vp ∧ P.vp < pTilde P * a - P.vbar / 2
    let C3 := fun p3 => P.c / P.q ≤ P.vbar ∧ p3 * b ≤ P.vp ∧ P.vp ≤ P.vbar * b
    let C4 := fun p3 => P.c / P.q ≤ P.vbar ∧ P.vp < p3 * b
    let C5 := P.vbar < P.c / P.q ∧ P.vp ≤ P.c / P.q * a - P.vbar / 2
    (P.c / P.q ≤ P.vbar → ∃! p3, rootP p3) ∧
    (C1 → IsEqPriceO P (pTilde P) ∧ coversO P (pTilde P) ∧ ∀ p, IsEqPriceO P p → p = pTilde P) ∧
    (C2 → IsEqPriceO P p1 ∧ coversO P p1 ∧ ∀ p, IsEqPriceO P p → p = p1) ∧
    (∀ p3, rootP p3 →
      (C3 p3 → IsEqPriceO P p2 ∧ coversO P p2 ∧
        (p3 * b < P.vp → ∀ p, IsEqPriceO P p → p = p2)) ∧
      (C4 p3 → IsEqPriceO P (pHatStar P) ∧ ¬coversO P (pHatStar P) ∧
        (P.c / P.q < P.vbar → ∀ p, IsEqPriceO P p → p = pHatStar P))) ∧
    (C5 → (∀ p, 0 ≤ p → realizedProfitO P p ≤ 0) ∧ (∃ p, 0 ≤ p ∧ realizedProfitO P p = 0) ∧
      (∀ p, P.c / P.q < p → p < P.vbar / P.β → ¬coversO P p) ∧
      (P.vp < P.c / P.q * a - P.vbar / 2 → ¬coversO P (P.c / P.q))) ∧
    ((¬C1 ∧ ¬C2 ∧ ¬(∃ p3, rootP p3 ∧ C3 p3) ∧ ¬(∃ p3, rootP p3 ∧ C4 p3)) ↔ C5) := by
      obtain ⟨hn, hv, hc, hβ, hβ2, hq, hq1, hα, hα1, hlam, hvp⟩ := hS
      have hA1 : P.β * P.c < P.q * P.vbar := by
        have h1 : P.β * P.c / P.vbar < P.q := lt_of_lt_of_le hA (min_le_left _ _)
        rw [div_lt_iff₀ hv] at h1; linarith
      have hu : ∀ x, 0 ≤ u P.α P.lam x ↔ 0 ≤ x := by
        intro x
        unfold u
        split_ifs with h
        · exact ⟨fun _ => h, fun _ => Real.rpow_nonneg h _⟩
        · constructor
          · intro h'
            have : 0 < (-x) ^ P.α := Real.rpow_pos_of_pos (by linarith) _
            linarith only [h', mul_pos (by linarith only [hlam] : (0:ℝ) < P.lam) this]
          · intro h'; exact absurd h' h
      have hbuy : ∀ bb p, 0 ≤ bb * p → buyersO P bb p = Set.Icc (bb * p) P.vbar := by
        intro bb p hbp
        ext v
        simp only [buyersO, welfareO, Set.mem_ofPred_eq, Set.mem_Icc]
        rw [mul_nonneg_iff_of_pos_left hq, hu]
        constructor
        · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨by linarith, h2⟩
        · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, h2⟩, by linarith⟩
      have hvol : ∀ bb p, 0 ≤ bb * p →
          (MeasureTheory.volume (buyersO P bb p)).toReal = max 0 (P.vbar - bb * p) := by
        intro bb p hbp
        rw [hbuy bb p hbp, Real.volume_Icc, ENNReal.toReal_ofReal', max_comm]
      have hint : ∀ bb p, 0 ≤ bb * p →
          ∫ v in buyersO P bb p, P.q * (v - bb * p) = P.q * (max 0 (P.vbar - bb * p))^2 / 2 := by
        intro bb p hbp
        rw [hbuy bb p hbp]
        rcases le_or_gt (bb * p) P.vbar with h | h
        · rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h,
            max_eq_right (by linarith)]
          rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
            intervalIntegrable_const, integral_id, intervalIntegral.integral_const]
          simp only [smul_eq_mul]
          ring
        · rw [Set.Icc_eq_empty (by linarith), max_eq_left (by linarith)]; simp
      have hobj : ∀ bb p, 0 ≤ bb * p → payerObjO P bb p = P.n / P.vbar * P.q *
          (max 0 (P.vbar - bb*p) * (P.vp - (1 - bb) * p) + (max 0 (P.vbar - bb*p))^2/2) := by
        intro bb p hbp
        rw [payerObjO, payerPayoffO, patientPayoffO, demandO, hvol bb p hbp, hint bb p hbp]
        ring
      have hfirm : ∀ bb p, 0 ≤ bb * p → firmProfitO P bb p =
          (P.q * p - P.c) * (P.n / P.vbar * max 0 (P.vbar - bb*p)) := by
        intro bb p hbp; rw [firmProfitO, demandO, hvol bb p hbp]
      have hNq : 0 < P.n / P.vbar * P.q := by positivity
      have hcov : ∀ p, 0 ≤ p → (coversO P p ↔
          max 0 (P.vbar - 1*p) * (P.vp - (1 - 1) * p) + (max 0 (P.vbar - 1*p))^2/2 ≤
          max 0 (P.vbar - P.β*p) * (P.vp - (1 - P.β) * p) + (max 0 (P.vbar - P.β*p))^2/2) := by
        intro p hp
        rw [coversO, hobj 1 p (by linarith), hobj P.β p (by positivity)]
        exact ⟨fun h => le_of_mul_le_mul_left h hNq, fun h => mul_le_mul_of_nonneg_left h hNq.le⟩
      have hRC : ∀ p, coversO P p → realizedProfitO P p = firmProfitO P P.β p := by
        intro p h; unfold realizedProfitO shareO; rw [if_pos h]
      have hRN : ∀ p, ¬coversO P p → realizedProfitO P p = firmProfitO P 1 p := by
        intro p h; unfold realizedProfitO shareO; rw [if_neg h]
      have hQ : 0 < P.q * (P.n / P.vbar) := by positivity
      have hb1 : 0 < 1 - P.β := by linarith only [hβ2]
      have ha : 0 < 1 - P.β / 2 := by linarith only [hβ2]
      have hb : 0 < (1 - P.β) / 2 := by linarith only [hβ2]
      dsimp only
      set k := P.c / P.q with hkdef
      have hk0 : 0 < k := div_pos hc hq
      have hqk : P.c = P.q * k := by rw [hkdef]; field_simp
      set w := P.vbar / P.β with hwdef
      have hw : P.β * w = P.vbar := by rw [hwdef]; field_simp
      have hw0 : 0 < w := div_pos hv hβ
      have hkw : k < w := by
        have h1 : P.β * k < P.β * w := by
          rw [hw, hkdef, mul_div_assoc', div_lt_iff₀ hq]; linarith only [hA1]
        exact lt_of_mul_lt_mul_left h1 hβ.le
      have hvw : 2 * P.vbar ≤ w := by
        linarith only [mul_le_mul_of_nonneg_right hβ2 hw0.le, hw]
      have hpH : pHatStar P = (k + P.vbar) / 2 := by
        unfold pHatStar; rw [hkdef]; field_simp
      have hpT : pTilde P = (k + w) / 2 := by
        unfold pTilde; rw [hkdef, hwdef]; field_simp
      simp only [hpH, hpT]
      clear_value k w
      obtain ⟨Q, hQdef⟩ : ∃ Q, Q = P.q * (P.n / P.vbar) := ⟨_, rfl⟩
      rw [← hQdef] at hQ
      -- closed forms
      have hC' : ∀ p, 0 ≤ p → p ≤ w → firmProfitO P P.β p = Q * ((p - k) * (P.vbar - P.β * p)) := by
        intro p hp hpw
        rw [hfirm _ _ (mul_nonneg hβ.le hp),
          max_eq_right (by linarith only [mul_le_mul_of_nonneg_left hpw hβ.le, hw]), hqk, hQdef]; ring
      have hC : ∀ p, 0 ≤ p → p ≤ w → firmProfitO P P.β p = Q * (P.β * ((p - k) * (w - p))) := by
        intro p hp hpw; rw [hC' p hp hpw]; linear_combination (-(Q * (p - k))) * hw
      have hC0 : ∀ p, w ≤ p → firmProfitO P P.β p = 0 := by
        intro p hp
        rw [hfirm _ _ (mul_nonneg hβ.le (by linarith)),
          max_eq_left (by linarith only [mul_le_mul_of_nonneg_left hp hβ.le, hw]), mul_zero, mul_zero]
      have hN : ∀ p, 0 ≤ p → p ≤ P.vbar → firmProfitO P 1 p = Q * ((p - k) * (P.vbar - p)) := by
        intro p hp hpv
        rw [hfirm _ _ (by linarith only [hp]), max_eq_right (by linarith only [hpv]), hqk, hQdef]; ring
      have hN0 : ∀ p, P.vbar ≤ p → firmProfitO P 1 p = 0 := by
        intro p hp
        rw [hfirm _ _ (by linarith only [hp, hv]), max_eq_left (by linarith only [hp]), mul_zero, mul_zero]
      have cov_low : ∀ p, 0 ≤ p → p ≤ P.vbar →
          (coversO P p ↔ 0 ≤ p * (P.vp - (1 - P.β) / 2 * p)) := by
        intro p hp hpv
        rw [hcov p hp, max_eq_right (by linarith only [hpv]),
          max_eq_right (by linarith only [mul_le_mul_of_nonneg_right hβ2 hp, hpv, hp])]
        have e : (P.vbar - P.β * p) * (P.vp - (1 - P.β) * p) + (P.vbar - P.β * p) ^ 2 / 2 -
            ((P.vbar - 1 * p) * (P.vp - (1 - 1) * p) + (P.vbar - 1 * p) ^ 2 / 2) =
            (1 - P.β) * (p * (P.vp - (1 - P.β) / 2 * p)) := by ring
        constructor
        · intro h; exact (mul_nonneg_iff_of_pos_left hb1).mp (by linarith only [h, e])
        · intro h; linarith only [mul_nonneg hb1.le h, e]
      have cov_mid : ∀ p, P.vbar ≤ p → p ≤ w →
          (coversO P p ↔ 0 ≤ (w - p) * (P.vp + P.vbar / 2 - (1 - P.β / 2) * p)) := by
        intro p hpv hpw
        have e1 : P.vbar - P.β * p = P.β * (w - p) := by linear_combination -hw
        rw [hcov p (by linarith only [hpv, hv]), max_eq_left (by linarith only [hpv]), e1,
          max_eq_right (mul_nonneg hβ.le (by linarith only [hpw]))]
        have e : P.β * (w - p) * (P.vp - (1 - P.β) * p) + (P.β * (w - p)) ^ 2 / 2 -
            (0 * (P.vp - (1 - 1) * p) + 0 ^ 2 / 2) =
            P.β * ((w - p) * (P.vp + P.vbar / 2 - (1 - P.β / 2) * p)) := by
          linear_combination (P.β * (w - p) / 2) * hw
        constructor
        · intro h; exact (mul_nonneg_iff_of_pos_left hβ).mp (by linarith only [h, e])
        · intro h; linarith only [mul_nonneg hβ.le h, e]
      have cov_high : ∀ p, w ≤ p → coversO P p := by
        intro p hp
        rw [hcov p (by linarith only [hp, hw0]), max_eq_left (by linarith only [hp, hvw, hv]),
          max_eq_left (by linarith only [mul_le_mul_of_nonneg_left hp hβ.le, hw])]; linarith only []
      -- bounds
      have B1 : ∀ p, 0 ≤ p → firmProfitO P 1 p ≤ Q * ((P.vbar - k) ^ 2 / 4) := by
        intro p hp
        rcases le_total p P.vbar with hpv | hpv
        · rw [hN p hp hpv]
          exact mul_le_mul_of_nonneg_left (by linarith only [sq_nonneg (p - (k + P.vbar) / 2)]) hQ.le
        · rw [hN0 p hpv]; positivity
      have B1eq : ∀ p, 0 ≤ p → k < P.vbar → Q * ((P.vbar - k) ^ 2 / 4) ≤ firmProfitO P 1 p →
          p = (k + P.vbar) / 2 := by
        intro p hp hkv h
        have hpos : 0 < Q * ((P.vbar - k) ^ 2 / 4) := by
          have : 0 < (P.vbar - k) ^ 2 := pow_pos (by linarith) 2
          positivity
        rcases le_total p P.vbar with hpv | hpv
        · rw [hN p hp hpv] at h
          have h2 := le_of_mul_le_mul_left h hQ
          have h3 : (p - (k + P.vbar) / 2) ^ 2 = 0 :=
            le_antisymm (by linarith only [h2]) (sq_nonneg _)
          have h4 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3
          linarith only [h4]
        · rw [hN0 p hpv] at h; linarith only [h, hpos]
      have B2 : ∀ p, 0 ≤ p → firmProfitO P P.β p ≤ Q * (P.β * ((w - k) ^ 2 / 4)) := by
        intro p hp
        rcases le_total p w with hpw | hpw
        · rw [hC p hp hpw]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            (by linarith only [sq_nonneg (p - (k + w) / 2)]) hβ.le) hQ.le
        · rw [hC0 p hpw]; positivity
      have hBpos : 0 < Q * (P.β * ((w - k) ^ 2 / 4)) := by
        have : 0 < (w - k) ^ 2 := pow_pos (by linarith) 2
        positivity
      have B2eq : ∀ p, 0 ≤ p → Q * (P.β * ((w - k) ^ 2 / 4)) ≤ firmProfitO P P.β p →
          p = (k + w) / 2 := by
        intro p hp h
        rcases le_total p w with hpw | hpw
        · rw [hC p hp hpw] at h
          have h2 := le_of_mul_le_mul_left (le_of_mul_le_mul_left h hQ) hβ
          have h3 : (p - (k + w) / 2) ^ 2 = 0 :=
            le_antisymm (by linarith only [h2]) (sq_nonneg _)
          have h4 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3
          linarith only [h4]
        · rw [hC0 p hpw] at h; linarith only [h, hBpos]
      have B3 : ∀ p x, 0 ≤ p → p < x → x ≤ (k + w) / 2 →
          firmProfitO P P.β p < firmProfitO P P.β x := by
        intro p x hp hpx hx
        rw [hC p hp (by linarith only [hpx, hx, hkw]), hC x (by linarith only [hp, hpx])
          (by linarith only [hx, hkw])]
        apply mul_lt_mul_of_pos_left _ hQ
        apply mul_lt_mul_of_pos_left _ hβ
        linarith only [mul_pos (sub_pos.2 hpx) (show 0 < k + w - x - p by linarith only [hpx, hx])]
      have B3le : ∀ p x, 0 ≤ p → p ≤ x → x ≤ (k + w) / 2 →
          firmProfitO P P.β p ≤ firmProfitO P P.β x := by
        intro p x hp hpx hx
        rcases eq_or_lt_of_le hpx with h | h
        · rw [h]
        · exact (B3 p x hp h hx).le
      have B4 : ∀ p, 0 ≤ p → firmProfitO P 1 p ≤ 0 ∨ firmProfitO P 1 p < firmProfitO P P.β p := by
        intro p hp
        rcases le_total P.vbar p with hpv | hpv
        · left; rw [hN0 p hpv]
        rcases le_total p k with hpk | hpk
        · left; rw [hN p hp hpv]
          linarith only [mul_nonneg (mul_nonneg hQ.le (sub_nonneg.2 hpk)) (sub_nonneg.2 hpv)]
        · rcases eq_or_lt_of_le hpk with h | h
          · left; rw [hN p hp hpv, ← h, sub_self, zero_mul, mul_zero]
          right
          rw [hN p hp hpv, hC' p hp (by linarith only [hpv, hvw, hv])]
          apply mul_lt_mul_of_pos_left _ hQ
          linarith only [mul_pos (mul_pos (sub_pos.2 h) hb1) (show 0 < p by linarith only [h, hk0])]
      have hCneg : ∀ p, 0 ≤ p → p ≤ k → firmProfitO P P.β p ≤ 0 := by
        intro p hp hpk
        rw [hC p hp (by linarith only [hpk, hkw])]
        have : 0 ≤ (k - p) * (w - p) := mul_nonneg (by linarith only [hpk]) (by linarith only [hpk, hkw])
        linarith only [mul_nonneg hQ.le (mul_nonneg hβ.le this)]
      have hNneg : ∀ p, 0 ≤ p → p ≤ k → firmProfitO P 1 p ≤ 0 := by
        intro p hp hpk
        rcases B4 p hp with h | h
        · exact h
        · linarith only [h, hCneg p hp hpk]
      clear hu hbuy hvol hint hobj hNq hcov hfirm hA hC' hkdef hwdef hpH hpT hQdef hA1
      have part1 : k ≤ P.vbar → ∃! p3, p3 ∈ Set.Icc k ((k + P.vbar) / 2) ∧
          firmProfitO P 1 ((k + P.vbar) / 2) = firmProfitO P P.β p3 := by
        intro hkv
        have hT : firmProfitO P 1 ((k + P.vbar) / 2) = Q * ((P.vbar - k) ^ 2 / 4) := by
          rw [hN _ (by linarith only [hk0, hv]) (by linarith only [hkv])]; ring
        have hcont : ContinuousOn (fun p => Q * (P.β * ((p - k) * (w - p))))
            (Set.Icc k ((k + P.vbar) / 2)) := by fun_prop
        have hlo : Q * (P.β * ((k - k) * (w - k))) ≤ Q * ((P.vbar - k) ^ 2 / 4) := by
          rw [sub_self, zero_mul, mul_zero, mul_zero]; positivity
        have hhi : Q * ((P.vbar - k) ^ 2 / 4) ≤
            Q * (P.β * (((k + P.vbar) / 2 - k) * (w - (k + P.vbar) / 2))) := by
          apply mul_le_mul_of_nonneg_left _ hQ.le
          have e : P.β * (((k + P.vbar) / 2 - k) * (w - (k + P.vbar) / 2)) =
              ((P.vbar - k) / 2) * (P.vbar - P.β * ((k + P.vbar) / 2)) := by
            linear_combination ((P.vbar - k) / 2) * hw
          rw [e]
          have : 0 ≤ (P.vbar - k) / 2 * ((1 - P.β) * ((k + P.vbar) / 2)) :=
            mul_nonneg (by linarith only [hkv]) (mul_nonneg hb1.le (by linarith only [hk0, hv]))
          linarith only [this]
        obtain ⟨x, hx, hfx⟩ := intermediate_value_Icc (by linarith only [hkv] : k ≤ (k + P.vbar) / 2)
          hcont ⟨hlo, hhi⟩
        beta_reduce at hfx
        have hxw : x ≤ w := by linarith only [hx.2, hkv, hvw, hv]
        refine ⟨x, ⟨hx, ?_⟩, ?_⟩
        · rw [hT, hC x (by linarith only [hx.1, hk0]) hxw]; exact hfx.symm
        · rintro y ⟨hy, hfy⟩
          rw [hT, hC y (by linarith only [hy.1, hk0]) (by linarith only [hy.2, hkv, hvw, hv])] at hfy
          have e := hfy.symm.trans hfx.symm
          have h2 : (y - k) * (w - y) = (x - k) * (w - x) :=
            mul_left_cancel₀ hβ.ne' (mul_left_cancel₀ hQ.ne' e)
          have h1 : (y - x) * (k + w - x - y) = 0 := by linear_combination h2
          rcases mul_eq_zero.mp h1 with h | h
          · linarith only [h]
          · exfalso; linarith only [h, hx.2, hy.2, hvw, hv]
      have hpT0 : 0 ≤ (k + w) / 2 := by linarith only [hk0, hw0]
      have hpTw : (k + w) / 2 < w := by linarith only [hkw]
      have hpTv : P.vbar < (k + w) / 2 := by linarith only [hk0, hvw]
      have hCpT : firmProfitO P P.β ((k + w) / 2) = Q * (P.β * ((w - k) ^ 2 / 4)) := by
        rw [hC _ hpT0 hpTw.le]; ring
      refine ⟨part1, ?_, ?_, ?_, ?_, ?_⟩
      · intro h1
        have hcovT : coversO P ((k + w) / 2) :=
          (cov_mid _ hpTv.le hpTw.le).2 (mul_nonneg (by linarith only [hpTw]) (by linarith only [h1]))
        refine ⟨⟨hpT0, fun p' hp' => ?_⟩, hcovT, fun p hp => ?_⟩
        · rw [hRC _ hcovT, hCpT]
          by_cases hc' : coversO P p'
          · rw [hRC _ hc']; exact B2 p' hp'
          · rw [hRN _ hc']
            rcases B4 p' hp' with h | h
            · linarith only [h, hBpos]
            · linarith only [h, B2 p' hp']
        · obtain ⟨hp0, hpmax⟩ := hp
          have h := hpmax _ hpT0
          rw [hRC _ hcovT, hCpT] at h
          by_cases hc' : coversO P p
          · rw [hRC _ hc'] at h; exact B2eq p hp0 h
          · rw [hRN _ hc'] at h
            exfalso
            rcases B4 p hp0 with h' | h'
            · linarith only [h, h', hBpos]
            · linarith only [h, h', B2 p hp0]
      · rintro ⟨h1, h2⟩
        have hp1 : (P.vp + P.vbar / 2) / (1 - P.β / 2) * (1 - P.β / 2) = P.vp + P.vbar / 2 :=
          div_mul_cancel₀ _ ha.ne'
        generalize (P.vp + P.vbar / 2) / (1 - P.β / 2) = p1 at hp1 ⊢
        have hm1 : max k P.vbar < p1 := lt_of_mul_lt_mul_right (by linarith only [h1, hp1]) ha.le
        have hk1 : k < p1 := lt_of_le_of_lt (le_max_left _ _) hm1
        have hv1 : P.vbar < p1 := lt_of_le_of_lt (le_max_right _ _) hm1
        have h1T : p1 < (k + w) / 2 := lt_of_mul_lt_mul_right (by linarith only [h2, hp1]) ha.le
        have hbv : (1 - P.β) / 2 * P.vbar < P.vp := by
          linarith only [h1, mul_le_mul_of_nonneg_right (le_max_right k P.vbar) ha.le]
        have hp10 : 0 ≤ p1 := by linarith only [hk1, hk0]
        have hcov1 : coversO P p1 := (cov_mid _ hv1.le (by linarith only [h1T, hpTw])).2
          (by rw [show P.vp + P.vbar / 2 - (1 - P.β / 2) * p1 = 0 by linarith only [hp1], mul_zero])
        have hpos1 : 0 < firmProfitO P P.β p1 := by
          rw [hC p1 hp10 (by linarith only [h1T, hpTw])]
          exact mul_pos hQ (mul_pos hβ (mul_pos (by linarith only [hk1])
            (by linarith only [h1T, hpTw])))
        have hcovC : ∀ p', coversO P p' → p' < w → p' ≤ p1 := by
          intro p' hc hpw
          by_contra hgt; push Not at hgt
          have h3 := (cov_mid p' (by linarith only [hgt, hv1]) hpw.le).1 hc
          have h4 := mul_lt_mul_of_pos_right hgt ha
          linarith only [h3, mul_pos (sub_pos.2 hpw)
            (show 0 < (1 - P.β / 2) * p' - (P.vp + P.vbar / 2) by linarith only [h4, hp1])]
        have hunc : ∀ p', 0 ≤ p' → ¬coversO P p' → P.vbar < p' := by
          intro p' hp' hc
          by_contra hle; push Not at hle
          exact hc ((cov_low p' hp' hle).2 (mul_nonneg hp'
            (by linarith only [hbv, mul_le_mul_of_nonneg_left hle hb.le])))
        refine ⟨⟨hp10, fun p' hp' => ?_⟩, hcov1, fun p hp => ?_⟩
        · rw [hRC _ hcov1]
          by_cases hc' : coversO P p'
          · rw [hRC _ hc']
            rcases lt_or_ge p' w with hpw | hpw
            · exact B3le p' p1 hp' (hcovC p' hc' hpw) h1T.le
            · rw [hC0 _ hpw]; exact hpos1.le
          · rw [hRN _ hc', hN0 _ (hunc p' hp' hc').le]; exact hpos1.le
        · obtain ⟨hp0, hpmax⟩ := hp
          have h := hpmax _ hp10
          rw [hRC _ hcov1] at h
          by_cases hc' : coversO P p
          · rw [hRC _ hc'] at h
            rcases lt_or_ge p w with hpw | hpw
            · rcases eq_or_lt_of_le (hcovC p hc' hpw) with he | hlt
              · exact he
              · linarith only [h, B3 p p1 hp0 hlt h1T.le]
            · rw [hC0 _ hpw] at h; linarith only [h, hpos1]
          · rw [hRN _ hc', hN0 _ (hunc p hp0 hc').le] at h; linarith only [h, hpos1]
      · rintro p3 ⟨⟨hk3, h3H⟩, hroot⟩
        have hpHv : (k + P.vbar) / 2 ≤ P.vbar := by linarith only [h3H, hk3]
        have hpH0 : 0 < (k + P.vbar) / 2 := by linarith only [hk0, hv]
        have hV : firmProfitO P 1 ((k + P.vbar) / 2) = Q * ((P.vbar - k) ^ 2 / 4) := by
          rw [hN _ hpH0.le hpHv]; ring
        have hV0 : 0 ≤ Q * ((P.vbar - k) ^ 2 / 4) := by positivity
        have h30 : 0 ≤ p3 := by linarith only [hk3, hk0]
        have h3T : p3 ≤ (k + w) / 2 := by linarith only [h3H, hpHv, hpTv]
        have hvmid : ∀ p', P.vbar < p' → p' < w → P.vp ≤ (1 - P.β) / 2 * P.vbar →
            ¬coversO P p' := by
          intro p' h1 h2 h3 hc
          have h4 := (cov_mid p' h1.le h2.le).1 hc
          have h5 := mul_lt_mul_of_pos_left h1 ha
          linarith only [h4, mul_pos (sub_pos.2 h2)
            (show 0 < (1 - P.β / 2) * p' - (P.vp + P.vbar / 2) by linarith only [h5, h3])]
        constructor
        · rintro ⟨hkv, h3b, hvb⟩
          have hp2 : 2 * P.vp / (1 - P.β) * ((1 - P.β) / 2) = P.vp := by field_simp
          generalize 2 * P.vp / (1 - P.β) = p2 at hp2 ⊢
          have hp20 : 0 ≤ p2 := by
            by_contra h; push Not at h; linarith only [mul_neg_of_neg_of_pos h hb, hp2, hvp]
          have h32 : p3 ≤ p2 := le_of_mul_le_mul_right (by linarith only [h3b, hp2]) hb
          have h2v : p2 ≤ P.vbar := le_of_mul_le_mul_right (by linarith only [hvb, hp2]) hb
          have h2T : p2 ≤ (k + w) / 2 := by linarith only [h2v, hpTv]
          have hcov2 : coversO P p2 := (cov_low p2 hp20 h2v).2
            (by rw [show P.vp - (1 - P.β) / 2 * p2 = 0 by linarith only [hp2], mul_zero])
          have hmono := B3le p3 p2 h30 h32 h2T
          have hcovC : ∀ p', 0 ≤ p' → coversO P p' → p' < w → p' ≤ p2 := by
            intro p' hp' hc hpw
            rcases le_or_gt p' P.vbar with hpv | hpv
            · have h4 := (cov_low p' hp' hpv).1 hc
              by_contra hgt; push Not at hgt
              have h5 := mul_lt_mul_of_pos_left hgt hb
              linarith only [h4, mul_pos (show 0 < p' by linarith only [hgt, hp20])
                (show 0 < (1 - P.β) / 2 * p' - P.vp by linarith only [h5, hp2])]
            · exact absurd hc (hvmid p' hpv hpw (by linarith only [hvb]))
          refine ⟨⟨hp20, fun p' hp' => ?_⟩, hcov2, fun hlt p hp => ?_⟩
          · rw [hRC _ hcov2]
            by_cases hc' : coversO P p'
            · rw [hRC _ hc']
              rcases lt_or_ge p' w with hpw | hpw
              · exact B3le p' p2 hp' (hcovC p' hp' hc' hpw) h2T
              · rw [hC0 _ hpw]; linarith only [hmono, hroot, hV, hV0]
            · rw [hRN _ hc']; linarith only [B1 p' hp', hmono, hroot, hV]
          · have h32' : p3 < p2 := lt_of_mul_lt_mul_right (by linarith only [hlt, hp2]) hb.le
            have hstr := B3 p3 p2 h30 h32' h2T
            obtain ⟨hp0, hpmax⟩ := hp
            have h := hpmax _ hp20
            rw [hRC _ hcov2] at h
            by_cases hc' : coversO P p
            · rw [hRC _ hc'] at h
              rcases lt_or_ge p w with hpw | hpw
              · rcases eq_or_lt_of_le (hcovC p hp0 hc' hpw) with he | hlt'
                · exact he
                · linarith only [h, B3 p p2 hp0 hlt' h2T]
              · rw [hC0 _ hpw] at h; linarith only [h, hstr, hroot, hV, hV0]
            · rw [hRN _ hc'] at h; linarith only [h, B1 p hp0, hstr, hroot, hV]
        · rintro ⟨hkv, h3b⟩
          have hbH : P.vp < (1 - P.β) / 2 * ((k + P.vbar) / 2) := by
            linarith only [h3b, mul_le_mul_of_nonneg_left h3H hb.le]
          have hncov : ¬coversO P ((k + P.vbar) / 2) := by
            intro hc
            have h4 := (cov_low _ hpH0.le hpHv).1 hc
            linarith only [h4, mul_pos hpH0
              (show 0 < (1 - P.β) / 2 * ((k + P.vbar) / 2) - P.vp by linarith only [hbH])]
          have hcovC : ∀ p', 0 ≤ p' → coversO P p' → p' < w → p' < p3 := by
            intro p' hp' hc hpw
            rcases le_or_gt p' P.vbar with hpv | hpv
            · have h4 := (cov_low p' hp' hpv).1 hc
              by_contra hge; push Not at hge
              have h5 := mul_le_mul_of_nonneg_left hge hb.le
              linarith only [h4, mul_pos (show 0 < p' by linarith only [hge, hk3, hk0])
                (show 0 < (1 - P.β) / 2 * p' - P.vp by linarith only [h5, h3b])]
            · exact absurd hc (hvmid p' hpv hpw
                (by linarith only [hbH, mul_le_mul_of_nonneg_left hpHv hb.le]))
          refine ⟨⟨hpH0.le, fun p' hp' => ?_⟩, hncov, fun hkv' p hp => ?_⟩
          · rw [hRN _ hncov]
            by_cases hc' : coversO P p'
            · rw [hRC _ hc']
              rcases lt_or_ge p' w with hpw | hpw
              · linarith only [B3le p' p3 hp' (hcovC p' hp' hc' hpw).le h3T, hroot]
              · rw [hC0 _ hpw]; linarith only [hV, hV0]
            · rw [hRN _ hc']; linarith only [B1 p' hp', hV]
          · obtain ⟨hp0, hpmax⟩ := hp
            have h := hpmax _ hpH0.le
            rw [hRN _ hncov, hV] at h
            have hVpos : 0 < Q * ((P.vbar - k) ^ 2 / 4) := by
              have : 0 < (P.vbar - k) ^ 2 := pow_pos (by linarith only [hkv']) 2
              positivity
            by_cases hc' : coversO P p
            · rw [hRC _ hc'] at h
              exfalso
              rcases lt_or_ge p w with hpw | hpw
              · linarith only [h, B3 p p3 hp0 (hcovC p hp0 hc' hpw) h3T, hroot, hV]
              · rw [hC0 _ hpw] at h; linarith only [h, hVpos]
            · rw [hRN _ hc'] at h; exact B1eq p hp0 hkv' h
      · rintro ⟨h1, h2⟩
        have hcovC5 : ∀ p, k < p → p < w → ¬coversO P p := by
          intro p hkp hpw hc
          have h4 := (cov_mid p (by linarith only [hkp, h1]) hpw.le).1 hc
          have h5 := mul_lt_mul_of_pos_left hkp ha
          linarith only [h4, mul_pos (sub_pos.2 hpw)
            (show 0 < (1 - P.β / 2) * p - (P.vp + P.vbar / 2) by linarith only [h5, h2])]
        refine ⟨fun p hp => ?_, ⟨k, hk0.le, ?_⟩, hcovC5, fun h3 hc => ?_⟩
        · by_cases hc' : coversO P p
          · rw [hRC _ hc']
            rcases le_or_gt p k with hpk | hpk
            · exact hCneg p hp hpk
            · rcases lt_or_ge p w with hpw | hpw
              · exact absurd hc' (hcovC5 p hpk hpw)
              · rw [hC0 _ hpw]
          · rw [hRN _ hc']
            rcases le_or_gt p k with hpk | hpk
            · exact hNneg p hp hpk
            · rw [hN0 _ (by linarith only [hpk, h1])]
        · by_cases hc' : coversO P k
          · rw [hRC _ hc', hC k hk0.le hkw.le, sub_self, zero_mul, mul_zero, mul_zero]
          · rw [hRN _ hc', hN0 _ h1.le]
        · have h4 := (cov_mid k h1.le hkw.le).1 hc
          linarith only [h4, mul_pos (sub_pos.2 hkw)
            (show 0 < (1 - P.β / 2) * k - (P.vp + P.vbar / 2) by linarith only [h3])]
      · constructor
        · rintro ⟨n1, n2, n3, n4⟩
          by_cases hkv : k ≤ P.vbar
          · exfalso
            obtain ⟨p3, hr, -⟩ := part1 hkv
            by_cases h : P.vp < p3 * ((1 - P.β) / 2)
            · exact n4 ⟨p3, hr, hkv, h⟩
            · push Not at h
              by_cases h' : P.vp ≤ P.vbar * ((1 - P.β) / 2)
              · exact n3 ⟨p3, hr, hkv, h, h'⟩
              · push Not at h'
                by_cases h'' : (k + w) / 2 * (1 - P.β / 2) - P.vbar / 2 ≤ P.vp
                · exact n1 h''
                · push Not at h''
                  exact n2 ⟨by rw [max_eq_right hkv]; linarith only [h'], h''⟩
          · push Not at hkv
            refine ⟨hkv, ?_⟩
            by_contra hc; push Not at hc
            by_cases h'' : (k + w) / 2 * (1 - P.β / 2) - P.vbar / 2 ≤ P.vp
            · exact n1 h''
            · push Not at h''
              exact n2 ⟨by rw [max_eq_left hkv.le]; exact hc, h''⟩
        · rintro ⟨h1, h2⟩
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro h
            have h5 := mul_lt_mul_of_pos_right (show k < (k + w) / 2 by linarith only [hkw]) ha
            linarith only [h, h2, h5]
          · rintro ⟨h3, h4⟩
            rw [max_eq_left h1.le] at h3; linarith only [h3, h2]
          · rintro ⟨p3, hr, hkv, -⟩; linarith only [hkv, h1]
          · rintro ⟨p3, hr, hkv, -⟩; linarith only [hkv, h1]
