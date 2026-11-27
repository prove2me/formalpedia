-- Prove2me | solution 1 for OutcomeRebate.Transfer.Supplement.proposition_8
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:06:52.524954+00:00
-- url     : https://prove2.me/submissions/760dbc40-4712-4cd9-859f-020c4079123a

import Mathlib
import Definitions.Def_OutcomeRebate_Transfer_Model
import Definitions.Def_OutcomeRebate_Transfer_Supplement_CorrelatedBenefit

open OutcomeRebate
open OutcomeRebate.Transfer
open OutcomeRebate.Transfer.Supplement

theorem solution (P : Params) (hS : P.Standing) (k : ℝ) (hk : 0 < k) :
    (∀ p : ℝ, P.vbar / P.β ≤ p → payerObjKO P k 1 p = payerObjKO P k P.β p) ∧
    (∀ p : ℝ, 0 ≤ p → p < P.vbar / P.β →
      (1 / P.β ≤ k + 1 → coversKO P k p) ∧
      (2 / (P.β + 1) ≤ k + 1 → k + 1 < 1 / P.β →
        (p ≤ P.vbar → coversKO P k p) ∧
        (P.vbar < p → (coversKO P k p ↔ p ≤ pHat2 P k))) ∧
      (k + 1 < 2 / (P.β + 1) → 0 < p → ¬coversKO P k p)) ∧
    coversKO P k 0 := by
      have hn : 0 < P.n := hS.1
      have hv : 0 < P.vbar := hS.2.1
      have hb : 0 < P.β := hS.2.2.2.1
      have hbhalf : P.β ≤ 1 / 2 := hS.2.2.2.2.1
      have hq : 0 < P.q := hS.2.2.2.2.2.1
      have hlam : 1 ≤ P.lam := hS.2.2.2.2.2.2.2.2.2.1
      have hb1 : P.β < 1 := by linarith
      have hbuyers : ∀ bb p : ℝ, 0 ≤ bb * p → buyersO P bb p = Set.Icc (bb * p) P.vbar := by
        intro bb p hbp
        ext v
        have hw : 0 ≤ welfareO P bb p v ↔ bb * p ≤ v := by
          unfold welfareO u
          by_cases h : 0 ≤ v - bb * p
          · simp only [if_pos h]
            exact ⟨fun _ => by linarith, fun _ => mul_nonneg hq.le (Real.rpow_nonneg h _)⟩
          · simp only [if_neg h]
            have ht : 0 < P.lam * (-(v - bb * p)) ^ P.α :=
              mul_pos (by linarith) (Real.rpow_pos_of_pos (by linarith) _)
            have ht' := mul_pos hq ht
            constructor <;> intro hh <;> nlinarith
        simp only [buyersO, Set.mem_ofPred_eq, Set.mem_Icc, hw]
        constructor
        · rintro ⟨⟨_, hv'⟩, hb'⟩
          exact ⟨hb', hv'⟩
        · rintro ⟨hb', hv'⟩
          exact ⟨⟨le_trans hbp hb', hv'⟩, hb'⟩
      have hform : ∀ bb p : ℝ, 0 ≤ bb * p → bb * p ≤ P.vbar →
          payerObjKO P k bb p = P.n * P.q / P.vbar * (P.vbar - bb * p) *
            ((k + 1) * (P.vbar + bb * p) / 2 - p) := by
        intro bb p hbp htop
        unfold payerObjKO payerPayoffKO patientPayoffO
        rw [hbuyers bb p hbp]
        have hi1 : MeasureTheory.IntegrableOn (fun v : ℝ => P.q * (k * v - (1 - bb) * p))
            (Set.Icc (bb * p) P.vbar) := by
          apply Continuous.integrableOn_Icc
          fun_prop
        have hi2 : MeasureTheory.IntegrableOn (fun v : ℝ => P.q * (v - bb * p))
            (Set.Icc (bb * p) P.vbar) := by
          apply Continuous.integrableOn_Icc
          fun_prop
        rw [← mul_add, ← MeasureTheory.integral_add hi1 hi2]
        have he : (fun v : ℝ => P.q * (k * v - (1 - bb) * p) + P.q * (v - bb * p)) =
            (fun v : ℝ => P.q * ((k + 1) * v - p)) := by
          funext v
          ring
        rw [he, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le htop]
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_sub (by apply Continuous.intervalIntegrable; fun_prop)
            (by apply Continuous.intervalIntegrable; fun_prop),
          intervalIntegral.integral_const_mul, integral_id, intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring
      have hzero : ∀ bb p : ℝ, 0 ≤ bb * p → P.vbar ≤ bb * p →
          payerObjKO P k bb p = 0 := by
        intro bb p hbp htop
        rcases eq_or_lt_of_le htop with heq | hlt
        · rw [hform bb p hbp heq.ge]
          rw [← heq]
          ring
        · unfold payerObjKO payerPayoffKO patientPayoffO
          rw [hbuyers bb p hbp, Set.Icc_eq_empty_of_lt hlt]
          simp
      have hC : 0 < P.n * P.q / P.vbar := div_pos (mul_pos hn hq) hv
      constructor
      · intro p hp
        have hpp : 0 ≤ p := le_trans (div_pos hv hb).le hp
        have ht : P.vbar ≤ P.β * p := (div_le_iff₀ hb).mp hp |>.trans_eq (mul_comm _ _)
        rw [hzero 1 p (by simpa using hpp) (by nlinarith),
          hzero P.β p (mul_nonneg hb.le hpp) ht]
      constructor
      · intro p hp htop
        have hbt : P.β * p < P.vbar := by
          have := (lt_div_iff₀ hb).mp htop
          nlinarith
        have hbf := hform P.β p (mul_nonneg hb.le hp) hbt.le
        have hsmall : p ≤ P.vbar →
            (coversKO P k p ↔ 0 ≤ (k + 1) * (P.β + 1) * p - 2 * p) := by
          intro hple
          unfold coversKO
          rw [hbf, hform 1 p (by simpa using hp) (by simpa using hple)]
          simp only [one_mul]
          have hid :
              P.n * P.q / P.vbar * (P.vbar - P.β * p) *
                  ((k + 1) * (P.vbar + P.β * p) / 2 - p) -
              P.n * P.q / P.vbar * (P.vbar - p) *
                  ((k + 1) * (P.vbar + p) / 2 - p) =
              (P.n * P.q / P.vbar * (1 - P.β) * p / 2) *
                  ((k + 1) * (P.β + 1) * p - 2 * p) := by ring
          by_cases hp0 : p = 0
          · simp [hp0]
          · have hpos : 0 < P.n * P.q / P.vbar * (1 - P.β) * p / 2 :=
              div_pos (mul_pos (mul_pos hC (by linarith)) (lt_of_le_of_ne hp (Ne.symm hp0)))
                (by norm_num)
            rw [← sub_nonneg, hid, mul_nonneg_iff_of_pos_left hpos]
        have hlarge : P.vbar ≤ p →
            (coversKO P k p ↔ 0 ≤ (k + 1) * (P.vbar + P.β * p) - 2 * p) := by
          intro hple
          unfold coversKO
          rw [hzero 1 p (by simpa using hp) (by simpa using hple), hbf]
          rw [mul_nonneg_iff_of_pos_left (mul_pos hC (sub_pos.mpr hbt))]
          constructor <;> intro h <;> linarith
        have hlow : 2 ≤ (k + 1) * (P.β + 1) → p ≤ P.vbar → coversKO P k p := by
          intro htwo hple
          apply (hsmall hple).mpr
          nlinarith [mul_nonneg (sub_nonneg.mpr htwo) hp]
        refine ⟨?_, ?_, ?_⟩
        · intro hhigh
          have hbk : 1 ≤ P.β * (k + 1) := by
            have := (div_le_iff₀ hb).mp hhigh
            nlinarith
          rcases le_total p P.vbar with hple | hple
          · apply hlow _ hple
            nlinarith
          · apply (hlarge hple).mpr
            have hsp : p ≤ (k + 1) * P.β * p := by
              nlinarith [mul_nonneg (sub_nonneg.mpr hbk) hp]
            have hsv := mul_le_mul_of_nonneg_left hbt.le (show 0 ≤ k + 1 by linarith)
            nlinarith
        · intro hmid hhigh
          have htwo : 2 ≤ (k + 1) * (P.β + 1) := by
            exact (div_le_iff₀ (by linarith : 0 < P.β + 1)).mp hmid
          refine ⟨hlow htwo, ?_⟩
          intro hple
          rw [hlarge hple.le]
          have hbk : P.β * (k + 1) < 1 := by
            have := (lt_div_iff₀ hb).mp hhigh
            nlinarith
          unfold pHat2
          rw [le_div_iff₀ (by linarith : 0 < 2 - P.β * (k + 1))]
          constructor <;> intro h <;> nlinarith
        · intro hlowk hpp hcov
          have htwo : (k + 1) * (P.β + 1) < 2 := by
            exact (lt_div_iff₀ (by linarith : 0 < P.β + 1)).mp hlowk
          rcases le_total p P.vbar with hple | hple
          · have hh := (hsmall hple).mp hcov
            nlinarith [mul_neg_of_neg_of_pos (by linarith : (k + 1) * (P.β + 1) - 2 < 0) hpp]
          · have hh := (hlarge hple).mp hcov
            have hs := mul_le_mul_of_nonneg_left hple (show 0 ≤ k + 1 by linarith)
            have ht := mul_lt_mul_of_pos_right htwo hpp
            nlinarith
      · unfold coversKO
        rw [hform 1 0 (by simp) (by simpa using hv.le),
          hform P.β 0 (by simp) (by simpa using hv.le)]
        simp
