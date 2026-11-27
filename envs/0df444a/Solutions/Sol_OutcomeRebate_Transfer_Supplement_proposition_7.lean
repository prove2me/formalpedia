-- Prove2me | solution 1 for OutcomeRebate.Transfer.Supplement.proposition_7
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:06:13.246348+00:00
-- url     : https://prove2.me/submissions/667a66a8-3ca4-4bf8-993e-bd5edbb6a33e

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model
import Definitions.Def_OutcomeRebate_Transfer_Supplement_CorrelatedBenefit

open OutcomeRebate
open OutcomeRebate.Transfer
open OutcomeRebate.Transfer.Supplement

theorem solution (P : Params) (hS : P.Standing) (k : ℝ) (hk : 0 < k) :
    (∀ p : ℝ, P.vbar / (P.β * P.z) ≤ p → payerObjKU P k 1 p = payerObjKU P k P.β p) ∧
    (∀ p : ℝ, 0 ≤ p → p < P.vbar / (P.β * P.z) →
      (1 / (P.q * P.z * P.β) ≤ k + 1 → coversKU P k p) ∧
      (2 / (P.q * P.z * (P.β + 1)) ≤ k + 1 → k + 1 < 1 / (P.q * P.z * P.β) →
        (p ≤ P.vbar / P.z → coversKU P k p) ∧
        (P.vbar / P.z < p → (coversKU P k p ↔ p ≤ pHat1 P k))) ∧
      (k + 1 < 2 / (P.q * P.z * (P.β + 1)) → 0 < p → ¬coversKU P k p)) ∧
    coversKU P k 0 := by
      obtain ⟨hn, hvb, hc, hβ, hβ2, hq, hq1, hα, hα1, hlam, hvp⟩ := hS
      set c0 : ℝ := P.lam * (1 - P.q) / P.q with hc0
      have hc0pos : 0 < c0 := by
        rw [hc0]; apply div_pos _ hq; apply mul_pos (by linarith) (by linarith)
      have hzdef : P.z = 1 + c0 ^ (1 / P.α) := rfl
      have hr0 : 0 < c0 ^ (1 / P.α) := Real.rpow_pos_of_pos hc0pos _
      have hz1 : 1 < P.z := by rw [hzdef]; linarith
      have hz : 0 < P.z := by linarith
      -- purchase rule
      have hrule : ∀ x v : ℝ, 0 ≤ x → 0 ≤ v →
          (0 ≤ P.q * u P.α P.lam (v - x) + (1 - P.q) * u P.α P.lam (-x) ↔ x * P.z ≤ v) := by
        intro x v hx hv
        rcases hx.lt_or_eq with hx | hx
        · have hux : u P.α P.lam (-x) = -(P.lam * x ^ P.α) := by
            unfold u; rw [if_neg (by linarith), neg_neg]
          rw [hux]
          have hxa : 0 < x ^ P.α := Real.rpow_pos_of_pos hx _
          by_cases hvx : x ≤ v
          · have huv : u P.α P.lam (v - x) = (v - x) ^ P.α := by
              unfold u; rw [if_pos (by linarith)]
            rw [huv]
            have hkey : c0 * x ^ P.α = (c0 ^ (1 / P.α) * x) ^ P.α := by
              rw [Real.mul_rpow (le_of_lt hr0) hx.le, ← Real.rpow_mul hc0pos.le,
                one_div_mul_cancel (ne_of_gt hα), Real.rpow_one]
            have h1 : 0 ≤ P.q * (v - x) ^ P.α + (1 - P.q) * -(P.lam * x ^ P.α) ↔
                c0 * x ^ P.α ≤ (v - x) ^ P.α := by
              rw [hc0, div_mul_eq_mul_div, div_le_iff₀ hq]
              constructor <;> intro h <;> nlinarith
            rw [h1, hkey, Real.rpow_le_rpow_iff (by positivity) (by linarith) hα, hzdef]
            constructor <;> intro h <;> nlinarith
          · push Not at hvx
            have huv : u P.α P.lam (v - x) = -(P.lam * (-(v - x)) ^ P.α) := by
              unfold u; rw [if_neg (by linarith)]
            rw [huv]
            have : 0 < (-(v - x)) ^ P.α := Real.rpow_pos_of_pos (by linarith) _
            have hl : 0 < P.lam := by linarith
            have e1 := mul_pos hq (mul_pos hl this)
            have e2 := mul_pos (sub_pos.2 hq1) (mul_pos hl hxa)
            constructor
            · intro h; nlinarith
            · intro h; nlinarith
        · subst hx
          have h0 : u P.α P.lam (-0) = 0 := by
            unfold u; simp [Real.zero_rpow (ne_of_gt hα)]
          have h1 : u P.α P.lam (v - 0) = v ^ P.α := by
            unfold u; simp [hv]
          rw [h0, h1]
          simp only [mul_zero, add_zero, zero_mul]
          constructor
          · intro _; exact hv
          · intro _; exact mul_nonneg hq.le (Real.rpow_nonneg hv _)
      have hbuy : ∀ bb p : ℝ, 0 ≤ bb → 0 ≤ p → buyersU P bb p = Set.Icc (bb * p * P.z) P.vbar := by
        intro bb p hbb hp
        have h0 : 0 ≤ bb * p * P.z := by positivity
        ext v
        simp only [buyersU, welfareU, Set.mem_ofPred_eq, Set.mem_Icc]
        constructor
        · rintro ⟨⟨hv0, hv1⟩, hw⟩
          exact ⟨(hrule (bb * p) v (by positivity) hv0).1 hw, hv1⟩
        · rintro ⟨hv0, hv1⟩
          exact ⟨⟨by linarith, hv1⟩, (hrule (bb * p) v (by positivity) (by linarith)).2 hv0⟩
      set K : ℝ := P.q * (k + 1) with hK
      have hobj : ∀ bb p : ℝ, 0 ≤ bb → 0 ≤ p → payerObjKU P k bb p =
          P.n / P.vbar * ∫ v in Set.Icc (bb * p * P.z) P.vbar, (K * v - p) := by
        intro bb p hbb hp
        unfold payerObjKU payerPayoffKU patientPayoffU
        rw [hbuy bb p hbb hp, ← mul_add, ← MeasureTheory.integral_add]
        · congr 1
          apply MeasureTheory.integral_congr_ae
          filter_upwards with v
          rw [hK]; ring
        · exact (by fun_prop : Continuous fun v : ℝ =>
            P.q * (k * v - (1 - bb) * p) - (1 - P.q) * (1 - bb) * p).integrableOn_Icc
        · exact (by fun_prop : Continuous fun v : ℝ =>
            P.q * (v - bb * p) - (1 - P.q) * (bb * p)).integrableOn_Icc
      have hG1 : ∀ a p : ℝ, a ≤ P.vbar → ∫ v in Set.Icc a P.vbar, (K * v - p) =
          K * (P.vbar ^ 2 - a ^ 2) / 2 - p * (P.vbar - a) := by
        intro a p ha
        rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha,
          intervalIntegral.integral_sub
            ((by fun_prop : Continuous fun x : ℝ => K * x).intervalIntegrable _ _)
            intervalIntegrable_const, intervalIntegral.integral_const_mul, integral_id,
            intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
      have hG2 : ∀ a p : ℝ, P.vbar ≤ a → ∫ v in Set.Icc a P.vbar, (K * v - p) = 0 := by
        intro a p ha
        apply MeasureTheory.setIntegral_measure_zero
        rw [Real.volume_Icc, ENNReal.ofReal_eq_zero]; linarith
      have hnv : 0 < P.n / P.vbar := div_pos hn hvb
      have hcovIff : ∀ p : ℝ, 0 ≤ p → (coversKU P k p ↔
          ∫ v in Set.Icc (1 * p * P.z) P.vbar, (K * v - p) ≤
            ∫ v in Set.Icc (P.β * p * P.z) P.vbar, (K * v - p)) := by
        intro p hp
        unfold coversKU
        rw [hobj 1 p zero_le_one hp, hobj P.β p hβ.le hp]
        exact mul_le_mul_iff_of_pos_left hnv
      -- in case: covers ↔ 0 ≤ p²z(1-β)(Kz(1+β)-2)/2
      have hin : ∀ p : ℝ, 0 ≤ p → p * P.z ≤ P.vbar → (coversKU P k p ↔
          0 ≤ p ^ 2 * P.z * (1 - P.β) * (K * P.z * (1 + P.β) - 2) / 2) := by
        intro p hp hpz
        have hle : P.β * p * P.z ≤ 1 * p * P.z :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hp) hz.le
        rw [hcovIff p hp, hG1 _ _ (by linarith), hG1 _ _ (by linarith)]
        have e : (K * (P.vbar ^ 2 - (P.β * p * P.z) ^ 2) / 2 - p * (P.vbar - P.β * p * P.z)) -
            (K * (P.vbar ^ 2 - (1 * p * P.z) ^ 2) / 2 - p * (P.vbar - 1 * p * P.z)) =
            p ^ 2 * P.z * (1 - P.β) * (K * P.z * (1 + P.β) - 2) / 2 := by ring
        constructor <;> intro h <;> linarith
      have hout : ∀ p : ℝ, 0 ≤ p → P.vbar ≤ p * P.z → P.β * p * P.z ≤ P.vbar → (coversKU P k p ↔
          0 ≤ (P.vbar - P.β * p * P.z) * (K * (P.vbar + P.β * p * P.z) - 2 * p) / 2) := by
        intro p hp hpz hbz
        rw [hcovIff p hp, hG2 _ _ (by linarith), hG1 _ _ hbz]
        have e : (K * (P.vbar ^ 2 - (P.β * p * P.z) ^ 2) / 2 - p * (P.vbar - P.β * p * P.z)) =
            (P.vbar - P.β * p * P.z) * (K * (P.vbar + P.β * p * P.z) - 2 * p) / 2 := by ring
        constructor <;> intro h <;> linarith
      have hβ1 : 0 < 1 - P.β := by linarith
      refine ⟨?_, ?_, ?_⟩
      · intro p hp
        have hbz : P.vbar ≤ p * (P.β * P.z) := (div_le_iff₀ (by positivity)).1 hp
        have hp0 : 0 ≤ p := le_trans (by positivity) hp
        have hle : P.β * p * P.z ≤ 1 * p * P.z :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hp0) hz.le
        have e : p * (P.β * P.z) = P.β * p * P.z := by ring
        rw [hobj 1 p zero_le_one hp0, hobj P.β p hβ.le hp0, hG2 _ _ (by linarith),
          hG2 _ _ (by linarith)]
      · intro p hp0 hplt
        have hbz0 : p * (P.β * P.z) < P.vbar := (lt_div_iff₀ (by positivity)).1 hplt
        have hbz : P.β * p * P.z < P.vbar := by
          have e : p * (P.β * P.z) = P.β * p * P.z := by ring
          linarith
        have hK0 : 0 < K := by rw [hK]; positivity
        refine ⟨?_, ?_, ?_⟩
        · intro hk1
          have h1 : 1 ≤ (k + 1) * (P.q * P.z * P.β) := (div_le_iff₀ (by positivity)).1 hk1
          have h1' : 1 ≤ K * P.z * P.β := by rw [hK]; linarith
          have hKz : 0 ≤ K * P.z * (1 + P.β) - 2 := by
            have := mul_nonneg (mul_nonneg hK0.le hz.le) (show 0 ≤ 1 / 2 - P.β by linarith)
            linarith
          rcases le_total (p * P.z) P.vbar with hpz | hpz
          · rw [hin p hp0 hpz]
            have := mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg p) hz.le) hβ1.le) hKz
            linarith
          · rw [hout p hp0 hpz (by linarith)]
            have hA : 0 ≤ K * (P.vbar + P.β * p * P.z) - 2 * p := by
              have t1 := mul_le_mul_of_nonneg_left h1' hp0
              have t2 := mul_le_mul_of_nonneg_left hbz.le hK0.le
              linarith
            have := mul_nonneg (show 0 ≤ P.vbar - P.β * p * P.z by linarith) hA
            linarith
        · intro hk1 hk2
          have h1 : 2 ≤ (k + 1) * (P.q * P.z * (P.β + 1)) := (div_le_iff₀ (by positivity)).1 hk1
          have h2 : (k + 1) * (P.q * P.z * P.β) < 1 := (lt_div_iff₀ (by positivity)).1 hk2
          have h1' : 0 ≤ K * P.z * (1 + P.β) - 2 := by rw [hK]; linarith
          have h2' : K * P.z * P.β < 1 := by rw [hK]; linarith
          refine ⟨?_, ?_⟩
          · intro hpz
            have hpz' : p * P.z ≤ P.vbar := (le_div_iff₀ hz).1 hpz
            rw [hin p hp0 hpz']
            have := mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg p) hz.le) hβ1.le) h1'
            linarith
          · intro hpz
            have hpz' : P.vbar < p * P.z := (div_lt_iff₀ hz).1 hpz
            rw [hout p hp0 hpz'.le (by linarith)]
            have hd : 0 < 2 - P.β * P.z * P.q * (k + 1) := by rw [hK] at h2'; linarith
            have hpos : 0 < P.vbar - P.β * p * P.z := by linarith
            unfold pHat1
            rw [le_div_iff₀ hd]
            have e1 : P.vbar * P.q * (k + 1) = P.vbar * K := by rw [hK]; ring
            have e2 : P.β * P.z * P.q * (k + 1) = K * P.z * P.β := by rw [hK]; ring
            rw [e1, e2]
            constructor
            · intro h
              have : 0 ≤ K * (P.vbar + P.β * p * P.z) - 2 * p := by
                by_contra hc
                push Not at hc
                have := mul_neg_of_pos_of_neg hpos hc
                linarith
              linarith
            · intro h
              have : 0 ≤ K * (P.vbar + P.β * p * P.z) - 2 * p := by linarith
              have := mul_nonneg hpos.le this
              linarith
        · intro hk1 hp
          have h1 : (k + 1) * (P.q * P.z * (P.β + 1)) < 2 := (lt_div_iff₀ (by positivity)).1 hk1
          have h1' : K * P.z * (1 + P.β) - 2 < 0 := by rw [hK]; linarith
          rcases le_total (p * P.z) P.vbar with hpz | hpz
          · rw [hin p hp0 hpz]
            have h3 : 0 < p ^ 2 * P.z * (1 - P.β) := by positivity
            have := mul_neg_of_pos_of_neg h3 h1'
            linarith
          · rw [hout p hp0 hpz (by linarith)]
            have hA : K * (P.vbar + P.β * p * P.z) - 2 * p < 0 := by
              have : K * P.vbar ≤ K * (p * P.z) := mul_le_mul_of_nonneg_left hpz hK0.le
              have : (K * P.z * (1 + P.β) - 2) * p < 0 := mul_neg_of_neg_of_pos h1' hp
              linarith
            have := mul_neg_of_pos_of_neg (show 0 < P.vbar - P.β * p * P.z by linarith) hA
            linarith
      · unfold coversKU payerObjKU payerPayoffKU patientPayoffU buyersU welfareU
        simp
