-- Prove2me | solution 1 for OutcomeRebate.Transfer.Supplement.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:07:22.073616+00:00
-- url     : https://prove2.me/submissions/ed9b8900-8c77-4e0b-baae-7dbb7da57541

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model
import Definitions.Def_OutcomeRebate_Transfer_Supplement_CorrelatedBenefit
import Definitions.Def_OutcomeRebate_Transfer_Supplement_OutcomePrices

open OutcomeRebate
open OutcomeRebate.Transfer
open OutcomeRebate.Transfer.Supplement

theorem solution (P : Params) (hS : P.Standing) (hA : Assumption1 P) (k : ℝ) (hk : 0 < k) :
    (thresholdAPrime P ≤ k + 1 → IsEqPriceKO P k (pTilde P) ∧ coversKO P k (pTilde P) ∧
      ∀ p, IsEqPriceKO P k p → p = pTilde P) ∧
    (thresholdBPrime P ≤ k + 1 → k + 1 < thresholdAPrime P →
      IsEqPriceKO P k (pHat2 P k) ∧ coversKO P k (pHat2 P k) ∧
      ((P.c / P.q) < pHat2 P k → ∀ p, IsEqPriceKO P k p → p = pHat2 P k)) ∧
    (k + 1 < thresholdBPrime P → (P.c / P.q) ≤ P.vbar →
      IsEqPriceKO P k (pHatStar P) ∧ ¬coversKO P k (pHatStar P) ∧
      ((P.c / P.q) < P.vbar → ∀ p, IsEqPriceKO P k p → p = pHatStar P)) ∧
    (k + 1 < thresholdBPrime P → P.vbar < (P.c / P.q) →
      (∀ p, 0 ≤ p → realizedProfitKO P k p ≤ 0) ∧ (∃ p, 0 ≤ p ∧ realizedProfitKO P k p = 0) ∧
      (∀ p, (P.c / P.q) ≤ p → p < P.vbar / P.β → ¬coversKO P k p)) := by
        obtain ⟨hn, hv, hc, hb, hb2, hq, hq1, ha, ha1, hlam, hvp⟩ := hS
        have hN : 0 < P.n / P.vbar := div_pos hn hv
        have hu : ∀ x, 0 ≤ u P.α P.lam x ↔ 0 ≤ x := by
          intro x; unfold u; split_ifs with h
          · exact ⟨fun _ => h, fun _ => Real.rpow_nonneg h _⟩
          · push Not at h
            have : 0 < (-x) ^ P.α := Real.rpow_pos_of_pos (by linarith) _
            constructor
            · intro h'; linarith [mul_pos (by linarith : 0 < P.lam) this]
            · intro h'; linarith
        have hbuy : ∀ bb p, 0 ≤ bb*p → buyersO P bb p = Set.Icc (bb*p) P.vbar := by
          intro bb p hbp; ext v
          simp only [buyersO, welfareO, Set.mem_ofPred_eq, Set.mem_Icc]
          rw [mul_nonneg_iff_of_pos_left hq, hu]
          constructor
          · rintro ⟨⟨h0, h1⟩, h2⟩; exact ⟨by linarith, h1⟩
          · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, h2⟩, by linarith⟩
        have hvol : ∀ a, (MeasureTheory.volume (Set.Icc a P.vbar)).toReal = max (P.vbar - a) 0 := by
          intro a; rw [Real.volume_Icc, ENNReal.toReal_ofReal']
        have hint1 : ∀ a p, a ≤ P.vbar → ∫ v in Set.Icc a P.vbar, P.q*((k+1)*v - p)
            = P.q*((k+1)*(P.vbar^2 - a^2)/2 - p*(P.vbar - a)) := by
          intro a p ha
          rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha]
          rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun v => P.q*((k+1)*v^2/2 - p*v))]
          · ring
          · intro x _
            have h1 := hasDerivAt_pow 2 x
            have h2 := ((h1.const_mul ((k+1)/2)).sub ((hasDerivAt_id x).const_mul p)).const_mul P.q
            refine (h2.congr_deriv (by simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_one]; ring)).congr_of_eventuallyEq
              (Filter.Eventually.of_forall fun v => ?_)
            simp only [Pi.sub_apply, id]; ring
          · exact (by fun_prop : Continuous fun v : ℝ => P.q*((k+1)*v - p)).intervalIntegrable _ _
        have hint2 : ∀ a p, P.vbar < a → ∫ v in Set.Icc a P.vbar, P.q*((k+1)*v - p) = 0 := by
          intro a p ha
          rw [Set.Icc_eq_empty_of_lt ha]; simp
        have hobj : ∀ bb p, 0 ≤ bb*p → payerObjKO P k bb p
            = P.n / P.vbar * ∫ v in Set.Icc (bb*p) P.vbar, P.q*((k+1)*v - p) := by
          intro bb p h
          unfold payerObjKO payerPayoffKO patientPayoffO
          rw [hbuy bb p h, ← mul_add, ← MeasureTheory.integral_add]
          · congr 1
            refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun v _ => by ring)
          · exact (by fun_prop : Continuous fun v : ℝ => P.q * (k * v - (1 - bb) * p)).integrableOn_Icc
          · exact (by fun_prop : Continuous fun v : ℝ => P.q * (v - bb * p)).integrableOn_Icc
        have covLow : ∀ p, 0 ≤ p → p ≤ P.vbar → (coversKO P k p ↔
            (k+1)*(P.vbar^2 - p^2)/2 - p*(P.vbar - p) ≤ (k+1)*(P.vbar^2 - (P.β*p)^2)/2 - p*(P.vbar - P.β*p)) := by
          intro p hp hpv
          unfold coversKO
          rw [hobj 1 p (by simpa using hp), hobj P.β p (by positivity), one_mul, hint1 p p hpv,
            hint1 (P.β*p) p (by linarith [mul_le_mul_of_nonneg_right (show P.β ≤ 1 by linarith) hp])]
          rw [mul_le_mul_iff_of_pos_left hN, mul_le_mul_iff_of_pos_left hq]
        have covMid : ∀ p, P.vbar ≤ p → P.β*p ≤ P.vbar → (coversKO P k p ↔
            0 ≤ (k+1)*(P.vbar^2 - (P.β*p)^2)/2 - p*(P.vbar - P.β*p)) := by
          intro p hp hbp
          have h0 : ∫ v in Set.Icc p P.vbar, P.q*((k+1)*v - p) = 0 := by
            rcases hp.lt_or_eq with h | h
            · exact hint2 p p h
            · rw [hint1 p p h.ge, h]; ring
          unfold coversKO
          rw [hobj 1 p (by simpa using (hv.le.trans hp)), hobj P.β p (mul_nonneg hb.le (hv.le.trans hp)), one_mul, h0,
            hint1 (P.β*p) p hbp, mul_zero, mul_nonneg_iff_of_pos_left hN, mul_nonneg_iff_of_pos_left hq]
        have hshare0 : ∀ p, 0 ≤ shareKO P k p := by
          intro p; unfold shareKO; split_ifs <;> linarith
        have hprof : ∀ p, 0 ≤ p → realizedProfitKO P k p
            = P.n / P.vbar * ((P.q*p - P.c) * max (P.vbar - shareKO P k p * p) 0) := by
          intro p hp
          unfold realizedProfitKO firmProfitO demandO
          rw [hbuy _ _ (mul_nonneg (hshare0 p) hp), hvol]; ring
        have hsh : ∀ p, (coversKO P k p ∧ shareKO P k p = P.β) ∨ (¬coversKO P k p ∧ shareKO P k p = 1) := by
          intro p; unfold shareKO; by_cases h : coversKO P k p
          · left; simp [h]
          · right; simp [h]
        obtain ⟨cq, hcq⟩ : ∃ cq, P.c = P.q * cq := ⟨P.c / P.q, by field_simp⟩
        have hcqd : P.c / P.q = cq := by rw [hcq]; field_simp
        rw [hcqd]
        have hcq0 : 0 < cq := pos_of_mul_pos_right (by rw [← hcq]; exact hc : 0 < P.q * cq) hq.le
        have hβcq : P.β * cq < P.vbar := by
          unfold Assumption1 at hA
          have h1 := lt_of_lt_of_le hA (min_le_left _ _)
          rw [div_lt_iff₀ hv, hcq] at h1
          exact lt_of_mul_lt_mul_left (by linarith : P.q*(P.β*cq) < P.q*P.vbar) hq.le
        have hsh' : ∀ p, P.β ≤ shareKO P k p ∧ shareKO P k p ≤ 1 := by
          intro p; rcases hsh p with h | h <;> rw [h.2] <;> constructor <;> linarith
        set pT := pTilde P with hpTdef
        have h2pT : 2*P.β*pT = P.β*cq + P.vbar := by
          rw [hpTdef]; unfold pTilde; rw [hcq]; field_simp
        have hpTv : P.vbar < pT := by
          by_contra h; push Not at h
          linarith [mul_le_mul_of_nonneg_left h (by linarith : (0:ℝ) ≤ 2*P.β), mul_pos hb hcq0,
            mul_le_mul_of_nonneg_left hb2 hv.le]
        have hβpT : P.β * pT < P.vbar := by linarith
        have hpT0 : 0 ≤ pT := by linarith
        have hcqT : cq < pT := by
          by_contra h; push Not at h
          linarith [mul_le_mul_of_nonneg_left h hb.le]
        have key : ∀ x, (P.q*pT - P.c)*(P.vbar - P.β*pT) - (P.q*x - P.c)*(P.vbar - P.β*x)
            = P.q*P.β*(x - pT)^2 := by
          intro x; rw [hcq]; linear_combination (P.q*(x - pT)) * h2pT
        have keyGen : ∀ x y, (P.q*y - P.c)*(P.vbar - P.β*y) - (P.q*x - P.c)*(P.vbar - P.β*x)
            = P.q*P.β*(y - x)*(2*pT - x - y) := by
          intro x y; rw [hcq]; linear_combination (P.q*(x - y)) * h2pT
        have hcovLo : 2 ≤ (k+1)*(1+P.β) → ∀ p, 0 ≤ p → p ≤ P.vbar → coversKO P k p := by
          intro hK p hp hpv
          rw [covLow p hp hpv]
          have : 0 ≤ p^2*(1-P.β)*((k+1)*(1+P.β) - 2) :=
            mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) (by linarith)
          linarith
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro hthr
          have hT : 2*(P.vbar + P.β*cq) ≤ (k+1)*P.β*(3*P.vbar + P.β*cq) := by
            unfold thresholdAPrime at hthr
            rw [div_le_iff₀ (by rw [hcq]; positivity)] at hthr
            have e1 : P.vbar*P.q + P.β*P.c = P.q*(P.vbar + P.β*cq) := by rw [hcq]; ring
            have e2 : 3*P.vbar*P.q + P.β*P.c = P.q*(3*P.vbar + P.β*cq) := by rw [hcq]; ring
            rw [e1, e2] at hthr
            have e3 : 2 / P.β * (P.q * (P.vbar + P.β * cq)) * P.β = P.q*(2*(P.vbar + P.β*cq)) := by
              field_simp
            have h4 := mul_le_mul_of_nonneg_right hthr hb.le
            rw [e3] at h4
            have h5 : P.q*(2*(P.vbar + P.β*cq)) ≤ P.q*((k+1)*P.β*(3*P.vbar + P.β*cq)) := by linarith
            exact le_of_mul_le_mul_left h5 hq
          have hfT : 0 < (P.q*pT - P.c)*(P.vbar - P.β*pT) := by
            rw [hcq]; apply mul_pos
            · linarith [mul_lt_mul_of_pos_left hcqT hq]
            · linarith
          have hcovT : coversKO P k pT := by
            rw [covMid pT hpTv.le hβpT.le]
            have e : P.β * (2*((k+1)*(P.vbar + P.β*pT)) - 4*pT) = (k+1)*P.β*(3*P.vbar + P.β*cq) - 2*(P.vbar + P.β*cq) := by
              linear_combination ((k+1)*P.β - 2) * h2pT
            have hK : 2*pT ≤ (k+1)*(P.vbar + P.β*pT) := by
              by_contra h; push Not at h
              linarith [mul_lt_mul_of_pos_left h hb]
            have e2 : (k + 1) * (P.vbar ^ 2 - (P.β * pT) ^ 2) / 2 - pT * (P.vbar - P.β * pT)
                = (P.vbar - P.β*pT) * (((k+1)*(P.vbar + P.β*pT) - 2*pT)/2) := by ring
            rw [e2]; apply mul_nonneg <;> linarith
          have hRT : realizedProfitKO P k pT = P.n / P.vbar * ((P.q*pT - P.c)*(P.vbar - P.β*pT)) := by
            rw [hprof pT hpT0, ((hsh pT).resolve_right (fun h => h.1 hcovT)).2, max_eq_left (by linarith)]
          refine ⟨⟨hpT0, ?_⟩, hcovT, ?_⟩
          · intro p hp
            rw [hRT, hprof p hp]
            apply mul_le_mul_of_nonneg_left _ hN.le
            have hs := hsh' p
            rcases le_or_gt (P.q*p - P.c) 0 with h1 | h1
            · linarith [mul_nonpos_of_nonpos_of_nonneg h1 (le_max_right (P.vbar - shareKO P k p * p) 0)]
            · rcases le_or_gt (P.vbar - shareKO P k p * p) 0 with h2 | h2
              · rw [max_eq_right h2]; linarith
              · rw [max_eq_left h2.le]
                have h3 : P.vbar - shareKO P k p * p ≤ P.vbar - P.β*p := by
                  linarith [mul_le_mul_of_nonneg_right hs.1 hp]
                have h4 : 0 ≤ P.q*P.β*(p - pT)^2 := by positivity
                linarith [mul_le_mul_of_nonneg_left h3 h1.le, key p]
          · rintro p ⟨hp0, hp⟩
            have h := hp pT hpT0
            rw [hRT, hprof p hp0] at h
            have h' := le_of_mul_le_mul_left h hN
            have hpos : 0 < P.q*p - P.c := by
              by_contra hneg; push Not at hneg
              linarith [mul_nonpos_of_nonpos_of_nonneg hneg (le_max_right (P.vbar - shareKO P k p * p) 0)]
            rcases le_or_gt (P.vbar - shareKO P k p * p) 0 with h2 | h2
            · rw [max_eq_right h2, mul_zero] at h'; linarith
            rw [max_eq_left h2.le] at h'
            have hp_pos : 0 < p := by
              by_contra hneg; push Not at hneg
              have := mul_le_mul_of_nonneg_left hneg hq.le
              rw [hcq] at hpos; linarith [mul_le_mul_of_nonneg_left hcq0.le hq.le]
            rcases hsh p with ⟨_, hs⟩ | ⟨_, hs⟩ <;> rw [hs] at h'
            · have h5 : P.q*P.β*(p-pT)^2 ≤ P.q*P.β*0 := by linarith [key p]
              have h6 : (p - pT)^2 ≤ 0 := le_of_mul_le_mul_left h5 (mul_pos hq hb)
              have : (p - pT)^2 = 0 := le_antisymm h6 (sq_nonneg _)
              exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
            · exfalso
              have h7 : 0 < (P.q*p - P.c) * ((1 - P.β) * p) := mul_pos hpos (mul_pos (by linarith) hp_pos)
              have h4 : 0 ≤ P.q*P.β*(p - pT)^2 := by positivity
              linarith [key p]
        · intro hB hA'
          have hm : 0 < max cq P.vbar := lt_of_lt_of_le hv (le_max_right _ _)
          unfold thresholdBPrime at hB
          rw [hcqd, div_le_iff₀ (by positivity)] at hB
          have hvm : P.vbar / max cq P.vbar ≤ 1 := (div_le_one hm).mpr (le_max_right _ _)
          have hvm2 : P.vbar / max cq P.vbar * cq ≤ P.vbar := by
            rw [div_mul_eq_mul_div, div_le_iff₀ hm]
            exact mul_le_mul_of_nonneg_left (le_max_left _ _) hv.le
          have hK0 : 0 ≤ k + 1 := by linarith
          have hB1 : 2 ≤ (k+1)*(1+P.β) := by
            linarith [mul_le_mul_of_nonneg_left hvm hK0]
          have hB2 : 2*cq ≤ (k+1)*(P.β*cq + P.vbar) := by
            have := mul_le_mul_of_nonneg_right hB hcq0.le
            linarith [mul_le_mul_of_nonneg_left hvm2 hK0]
          have hT : (k+1)*P.β*(3*P.vbar + P.β*cq) < 2*(P.vbar + P.β*cq) := by
            unfold thresholdAPrime at hA'
            rw [lt_div_iff₀ (by rw [hcq]; positivity)] at hA'
            have e1 : P.vbar*P.q + P.β*P.c = P.q*(P.vbar + P.β*cq) := by rw [hcq]; ring
            have e2 : 3*P.vbar*P.q + P.β*P.c = P.q*(3*P.vbar + P.β*cq) := by rw [hcq]; ring
            rw [e1, e2] at hA'
            have e3 : 2 / P.β * (P.q * (P.vbar + P.β * cq)) * P.β = P.q*(2*(P.vbar + P.β*cq)) := by
              field_simp
            have h4 := mul_lt_mul_of_pos_right hA' hb
            rw [e3] at h4
            have h5 : P.q*((k+1)*P.β*(3*P.vbar + P.β*cq)) < P.q*(2*(P.vbar + P.β*cq)) := by linarith
            exact lt_of_mul_lt_mul_left h5 hq.le
          have hKβ : (k+1)*P.β < 1 := by
            by_contra hneg; push Not at hneg
            have := mul_le_mul_of_nonneg_right hneg (by positivity : (0:ℝ) ≤ 3*P.vbar + P.β*cq)
            linarith
          have hd : 0 < 2 - P.β*(k+1) := by linarith
          set pH := pHat2 P k with hpHdef
          have h2pH : (2 - P.β*(k+1))*pH = P.vbar*(k+1) := by
            rw [hpHdef]; unfold pHat2; field_simp
          have hpHv : P.vbar ≤ pH := by
            refine le_of_mul_le_mul_left ?_ hd; rw [h2pH]; linarith [mul_le_mul_of_nonneg_left hB1 hv.le]
          have hβpH : P.β * pH < P.vbar := by
            refine lt_of_mul_lt_mul_left ?_ hd.le
            have : (2 - P.β*(k+1))*(P.β*pH) = P.β*(P.vbar*(k+1)) := by rw [← h2pH]; ring
            rw [this]; linarith [mul_lt_mul_of_pos_left hKβ hv]
          have hcqH : cq ≤ pH := by
            refine le_of_mul_le_mul_left ?_ hd; rw [h2pH]; linarith
          have hpH0 : 0 ≤ pH := by linarith
          have hpHT : pH < pT := by
            refine lt_of_mul_lt_mul_left ?_ hd.le
            rw [h2pH]
            have : 2*P.β*((2 - P.β*(k+1))*pT) = (2 - P.β*(k+1))*(P.β*cq + P.vbar) := by
              rw [← h2pT]; ring
            have h6 : 2*P.β*(P.vbar*(k+1)) < 2*P.β*((2 - P.β*(k+1))*pT) := by rw [this]; linarith
            exact lt_of_mul_lt_mul_left h6 (by positivity)
          have hcovH : coversKO P k pH := by
            rw [covMid pH hpHv hβpH.le]
            have e2 : (k + 1) * (P.vbar ^ 2 - (P.β * pH) ^ 2) / 2 - pH * (P.vbar - P.β * pH)
                = (P.vbar - P.β*pH) * ((P.vbar*(k+1) - (2 - P.β*(k+1))*pH)/2) := by ring
            rw [e2, h2pH, sub_self, zero_div, mul_zero]
          have hnc : ∀ p, pH < p → P.β*p < P.vbar → ¬coversKO P k p := by
            intro p hp hbp hcv
            rw [covMid p (by linarith) hbp.le] at hcv
            have e2 : (k + 1) * (P.vbar ^ 2 - (P.β * p) ^ 2) / 2 - p * (P.vbar - P.β * p)
                = (P.vbar - P.β*p) * ((P.vbar*(k+1) - (2 - P.β*(k+1))*p)/2) := by ring
            rw [e2] at hcv
            have h1 : (2 - P.β*(k+1))*pH < (2 - P.β*(k+1))*p := mul_lt_mul_of_pos_left hp hd
            have h2 : (P.vbar - P.β*p) * ((P.vbar*(k+1) - (2 - P.β*(k+1))*p)/2) < 0 :=
              mul_neg_of_pos_of_neg (by linarith) (by linarith)
            linarith
          have hfH : 0 ≤ (P.q*pH - P.c)*(P.vbar - P.β*pH) := by
            rw [hcq]; apply mul_nonneg
            · linarith [mul_le_mul_of_nonneg_left hcqH hq.le]
            · linarith
          have hRH : realizedProfitKO P k pH = P.n / P.vbar * ((P.q*pH - P.c)*(P.vbar - P.β*pH)) := by
            rw [hprof pH hpH0, ((hsh pH).resolve_right (fun h => h.1 hcovH)).2, max_eq_left (by linarith)]
          refine ⟨⟨hpH0, ?_⟩, hcovH, ?_⟩
          · intro p hp
            rw [hRH, hprof p hp]
            apply mul_le_mul_of_nonneg_left _ hN.le
            rcases le_or_gt (P.q*p - P.c) 0 with h1 | h1
            · linarith [mul_nonpos_of_nonpos_of_nonneg h1 (le_max_right (P.vbar - shareKO P k p * p) 0)]
            rcases le_or_gt (P.vbar - shareKO P k p * p) 0 with h2 | h2
            · rw [max_eq_right h2]; linarith
            rw [max_eq_left h2.le]
            rcases hsh p with ⟨hcv, hs⟩ | ⟨hcv, hs⟩ <;> rw [hs] at h2 ⊢
            · rcases le_or_gt p pH with h3 | h3
              · have : 0 ≤ P.q*P.β*(pH - p)*(2*pT - p - pH) :=
                  mul_nonneg (mul_nonneg (mul_pos hq hb).le (by linarith)) (by linarith)
                linarith [keyGen p pH]
              · exact absurd hcv (hnc p h3 (by linarith))
            · exact absurd (hcovLo hB1 p hp (by linarith)) hcv
          · intro hcqlt p ⟨hp0, hp⟩
            have h := hp pH hpH0
            rw [hRH, hprof p hp0] at h
            have h' := le_of_mul_le_mul_left h hN
            have hfH' : 0 < (P.q*pH - P.c)*(P.vbar - P.β*pH) := by
              rw [hcq]; apply mul_pos
              · linarith [mul_lt_mul_of_pos_left hcqlt hq]
              · linarith
            have hpos : 0 < P.q*p - P.c := by
              by_contra hneg; push Not at hneg
              linarith [mul_nonpos_of_nonpos_of_nonneg hneg (le_max_right (P.vbar - shareKO P k p * p) 0)]
            rcases le_or_gt (P.vbar - shareKO P k p * p) 0 with h2 | h2
            · rw [max_eq_right h2, mul_zero] at h'; linarith
            rw [max_eq_left h2.le] at h'
            rcases hsh p with ⟨hcv, hs⟩ | ⟨hcv, hs⟩ <;> rw [hs] at h' h2
            · rcases le_or_gt p pH with h3 | h3
              · by_contra hne
                have h4 : p < pH := lt_of_le_of_ne h3 hne
                have : 0 < P.q*P.β*(pH - p)*(2*pT - p - pH) :=
                  mul_pos (mul_pos (mul_pos hq hb) (by linarith)) (by linarith)
                linarith [keyGen p pH]
              · exact absurd hcv (hnc p h3 (by linarith))
            · exact absurd (hcovLo hB1 p hp0 (by linarith)) hcv
        · intro hB hcqv
          unfold thresholdBPrime at hB
          rw [hcqd, max_eq_right hcqv, div_self hv.ne', lt_div_iff₀ (by linarith)] at hB
          set pS := pHatStar P with hpSdef
          have h2pS : 2*pS = cq + P.vbar := by
            rw [hpSdef]; unfold pHatStar; rw [hcq]; field_simp; try ring
          have hpSv : pS ≤ P.vbar := by linarith
          have hpScq : cq ≤ pS := by linarith
          have hpS0 : 0 < pS := by linarith
          have hβpS : P.β*pS < P.vbar := by linarith [mul_le_mul_of_nonneg_right hb2 hpS0.le]
          have hnc : ∀ p, 0 < p → P.β*p < P.vbar → ¬coversKO P k p := by
            intro p hp hbp hcv
            rcases le_or_gt p P.vbar with hpv | hpv
            · rw [covLow p hp.le hpv] at hcv
              have : 0 < p^2*(1-P.β)*(2 - (k+1)*(P.β+1)) :=
                mul_pos (mul_pos (by positivity) (by linarith)) (by linarith)
              linarith
            · rw [covMid p hpv.le hbp.le] at hcv
              have e2 : (k + 1) * (P.vbar ^ 2 - (P.β * p) ^ 2) / 2 - p * (P.vbar - P.β * p)
                  = (P.vbar - P.β*p) * (((k+1)*(P.vbar + P.β*p) - 2*p)/2) := by ring
              rw [e2] at hcv
              have h3 : (k+1)*(P.vbar + P.β*p) - 2*p < 0 := by
                linarith [mul_lt_mul_of_pos_left hpv (by linarith : (0:ℝ) < k+1), mul_lt_mul_of_pos_right hB hp]
              linarith [mul_neg_of_pos_of_neg (by linarith : 0 < P.vbar - P.β*p) (by linarith : ((k+1)*(P.vbar + P.β*p) - 2*p)/2 < 0)]
          have keyS : ∀ x, (P.q*pS - P.c)*(P.vbar - pS) - (P.q*x - P.c)*(P.vbar - x) = P.q*(x - pS)^2 := by
            intro x; rw [hcq]; linear_combination (P.q*(x - pS)) * h2pS
          have hncS : ¬coversKO P k pS := hnc pS hpS0 hβpS
          have hRS : realizedProfitKO P k pS = P.n / P.vbar * ((P.q*pS - P.c)*(P.vbar - pS)) := by
            rw [hprof pS hpS0.le, ((hsh pS).resolve_left (fun h => hncS h.1)).2, one_mul,
              max_eq_left (by linarith)]
          have hgS : 0 ≤ (P.q*pS - P.c)*(P.vbar - pS) := by
            rw [hcq]; apply mul_nonneg
            · linarith [mul_le_mul_of_nonneg_left hpScq hq.le]
            · linarith
          refine ⟨⟨hpS0.le, ?_⟩, hncS, ?_⟩
          · intro p hp
            rw [hRS, hprof p hp]
            apply mul_le_mul_of_nonneg_left _ hN.le
            rcases le_or_gt (P.q*p - P.c) 0 with h1 | h1
            · linarith [mul_nonpos_of_nonpos_of_nonneg h1 (le_max_right (P.vbar - shareKO P k p * p) 0)]
            have hp_pos : 0 < p := by
              by_contra hneg; push Not at hneg
              rw [hcq] at h1; linarith [mul_le_mul_of_nonneg_left hneg hq.le, mul_pos hq hcq0]
            rcases le_or_gt (P.vbar - shareKO P k p * p) 0 with h2 | h2
            · rw [max_eq_right h2]; linarith
            rw [max_eq_left h2.le]
            rcases hsh p with ⟨hcv, hs⟩ | ⟨hcv, hs⟩ <;> rw [hs] at h2 ⊢
            · exact absurd hcv (hnc p hp_pos (by linarith))
            · have : 0 ≤ P.q*(p - pS)^2 := by positivity
              linarith [keyS p]
          · intro hlt p ⟨hp0, hp⟩
            have h := hp pS hpS0.le
            rw [hRS, hprof p hp0] at h
            have h' := le_of_mul_le_mul_left h hN
            have hgS' : 0 < (P.q*pS - P.c)*(P.vbar - pS) := by
              rw [hcq]; apply mul_pos
              · linarith [mul_lt_mul_of_pos_left (by linarith : cq < pS) hq]
              · linarith
            have hpos : 0 < P.q*p - P.c := by
              by_contra hneg; push Not at hneg
              linarith [mul_nonpos_of_nonpos_of_nonneg hneg (le_max_right (P.vbar - shareKO P k p * p) 0)]
            have hp_pos : 0 < p := by
              by_contra hneg; push Not at hneg
              rw [hcq] at hpos; linarith [mul_le_mul_of_nonneg_left hneg hq.le, mul_pos hq hcq0]
            rcases le_or_gt (P.vbar - shareKO P k p * p) 0 with h2 | h2
            · rw [max_eq_right h2, mul_zero] at h'; linarith
            rw [max_eq_left h2.le] at h'
            rcases hsh p with ⟨hcv, hs⟩ | ⟨hcv, hs⟩ <;> rw [hs] at h' h2
            · exact absurd hcv (hnc p hp_pos (by linarith))
            · have h5 : P.q*(p-pS)^2 ≤ P.q*0 := by linarith [keyS p]
              have h6 : (p - pS)^2 ≤ 0 := le_of_mul_le_mul_left h5 hq
              have : (p - pS)^2 = 0 := le_antisymm h6 (sq_nonneg _)
              exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
        · intro hB hvcq
          unfold thresholdBPrime at hB
          rw [hcqd, max_eq_left hvcq.le, lt_div_iff₀ (by positivity)] at hB
          have hB2 : (k+1)*(P.β*cq + P.vbar) < 2*cq := by
            have := mul_lt_mul_of_pos_right hB hcq0
            have e : (k+1)*(P.β + P.vbar/cq)*cq = (k+1)*(P.β*cq + P.vbar) := by field_simp
            linarith
          have hKβ : (k+1)*P.β < 2 := by
            have : (k+1)*P.β*cq < 2*cq := by
              linarith [mul_pos (by linarith : (0:ℝ) < k+1) hv]
            exact lt_of_mul_lt_mul_right this hcq0.le
          have hnc4 : ∀ p, cq ≤ p → p < P.vbar / P.β → ¬coversKO P k p := by
            intro p hp1 hp2 hcv
            have hbp : P.β*p < P.vbar := by rw [lt_div_iff₀ hb] at hp2; linarith
            have hpv : P.vbar < p := by linarith
            rw [covMid p hpv.le hbp.le] at hcv
            have e2 : (k + 1) * (P.vbar ^ 2 - (P.β * p) ^ 2) / 2 - p * (P.vbar - P.β * p)
                = (P.vbar - P.β*p) * (((k+1)*(P.vbar + P.β*p) - 2*p)/2) := by ring
            rw [e2] at hcv
            have h3 : (2 - (k+1)*P.β)*cq ≤ (2 - (k+1)*P.β)*p := mul_le_mul_of_nonneg_left hp1 (by linarith)
            have h4 : ((k+1)*(P.vbar + P.β*p) - 2*p)/2 < 0 := by linarith
            linarith [mul_neg_of_pos_of_neg (by linarith : 0 < P.vbar - P.β*p) h4]
          refine ⟨?_, ⟨cq, hcq0.le, ?_⟩, hnc4⟩
          · intro p hp
            rw [hprof p hp]
            apply mul_nonpos_of_nonneg_of_nonpos hN.le
            rcases le_or_gt (P.q*p - P.c) 0 with h1 | h1
            · exact mul_nonpos_of_nonpos_of_nonneg h1 (le_max_right _ _)
            have hpcq : cq < p := by
              by_contra hneg; push Not at hneg
              rw [hcq] at h1; linarith [mul_le_mul_of_nonneg_left hneg hq.le]
            rcases le_or_gt (P.vbar - shareKO P k p * p) 0 with h2 | h2
            · rw [max_eq_right h2, mul_zero]
            exfalso
            rcases hsh p with ⟨hcv, hs⟩ | ⟨hcv, hs⟩ <;> rw [hs] at h2
            · exact hnc4 p hpcq.le (by rw [lt_div_iff₀ hb]; linarith) hcv
            · linarith
          · rw [hprof cq hcq0.le, hcq, sub_self, zero_mul, mul_zero]
