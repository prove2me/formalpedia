-- Prove2me | solution 1 for ReactiveCapacity.retailer_stage_rule
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-12T01:49:52.820106+00:00
-- url     : https://prove2.me/submissions/756e91a8-b421-459c-a163-d9539efed5b4

import Mathlib
import Definitions.Def_ReactiveCapacity_Model
import Definitions.Def_ReactiveCapacity_Game

open ReactiveCapacity

theorem solution (P : Params) (hP : P.Standing) (q w S : ℝ) (hq : 0 < q) (hw0 : 0 ≤ w)
    (hw : w < q * P.θH) (hS : 0 ≤ S) :
    (∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      IsGreatest {v : ℝ | ∃ Q p : ℝ, 0 ≤ Q ∧ 0 ≤ p ∧ v = P.stepOnePayoff q w α S Q p}
        (max (max ((q * P.θH - w) * min α S) ((q * P.θL - w) * min S 1)) 0)) ∧
    (0 < S → ∀ Q p : ℝ, 0 ≤ Q → 0 ≤ p →
      (∀ Q' p' : ℝ, 0 ≤ Q' → 0 ≤ p' →
        P.stepOnePayoff q w P.αg S Q' p' ≤ P.stepOnePayoff q w P.αg S Q p) →
      p = q * P.θH) ∧
    ((q * P.θH - w) * min P.αb S < (q * P.θL - w) * min S 1 → ∀ Q p : ℝ, 0 ≤ Q → 0 ≤ p →
      (∀ Q' p' : ℝ, 0 ≤ Q' → 0 ≤ p' →
        P.stepOnePayoff q w P.αb S Q' p' ≤ P.stepOnePayoff q w P.αb S Q p) →
      p = q * P.θL) ∧
    ((q * P.θL - w) * min S 1 < (q * P.θH - w) * min P.αb S → ∀ Q p : ℝ, 0 ≤ Q → 0 ≤ p →
      (∀ Q' p' : ℝ, 0 ≤ Q' → 0 ≤ p' →
        P.stepOnePayoff q w P.αb S Q' p' ≤ P.stepOnePayoff q w P.αb S Q p) →
      p = q * P.θH) := by
  rcases hP with ⟨hθL, hθLH, _hk, _hρ0, _hρ1, hαb0, hαb_lt, hαg_gt, hαg1⟩
  have hθH : 0 < P.θH := lt_trans hθL hθLH
  have hqL : 0 < q * P.θL := mul_pos hq hθL
  have hqH : 0 < q * P.θH := mul_pos hq hθH
  have hqLH : q * P.θL < q * P.θH := mul_lt_mul_of_pos_left hθLH hq
  have hwH : 0 < q * P.θH - w := sub_pos.mpr hw
  have hαg0 : 0 < P.αg := pos_of_mul_pos_left (lt_trans hθL hαg_gt) hθH.le
  have hαb1 : P.αb < 1 := by
    by_contra h
    have hge : 1 ≤ P.αb := le_of_not_gt h
    have := mul_le_mul_of_nonneg_right hge hθH.le
    linarith
  have h_att0 : ∀ α : ℝ, P.stepOnePayoff q w α S 0 0 = 0 := by
    intro α
    simp [Params.stepOnePayoff, min_eq_left hS]
  have h_attH : ∀ α : ℝ, 0 ≤ α →
      P.stepOnePayoff q w α S (min α S) (q * P.θH) = (q * P.θH - w) * min α S := by
    intro α _hα0
    unfold Params.stepOnePayoff Params.demand
    rw [if_neg (not_le_of_gt hqLH), if_pos (le_refl _), zero_add,
      min_eq_left (min_le_right α S), min_eq_right (min_le_left α S)]
    ring
  have h_attL : ∀ α : ℝ,
      P.stepOnePayoff q w α S (min S 1) (q * P.θL) = (q * P.θL - w) * min S 1 := by
    intro α
    unfold Params.stepOnePayoff Params.demand
    rw [if_pos (le_refl _), if_pos hqLH.le, sub_add_cancel,
      min_eq_left (min_le_left S 1), min_eq_right (min_le_right S 1)]
    ring
  have h_caseL : ∀ α Q p : ℝ, 0 ≤ Q → p ≤ q * P.θL →
      P.stepOnePayoff q w α S Q p ≤ max ((q * P.θL - w) * min S 1) 0 ∧
      (p < q * P.θL → 0 < (q * P.θL - w) * min S 1 →
        P.stepOnePayoff q w α S Q p < (q * P.θL - w) * min S 1) := by
    intro α Q p hQ hp
    let r := min Q S
    have hr0 : 0 ≤ r := le_min hQ hS
    have hrS : r ≤ S := min_le_right Q S
    have hpay : P.stepOnePayoff q w α S Q p = p * min 1 r - w * r := by
      unfold Params.stepOnePayoff Params.demand
      rw [if_pos hp, if_pos (le_trans hp hqLH.le), sub_add_cancel]
    have hr1_0 : 0 ≤ min 1 r := le_min zero_le_one hr0
    have hr1_r : min 1 r ≤ r := min_le_right 1 r
    have hr1_S1 : min 1 r ≤ min S 1 :=
      le_min (le_trans (min_le_right 1 r) hrS) (min_le_left 1 r)
    have hwr : w * min 1 r ≤ w * r := mul_le_mul_of_nonneg_left hr1_r hw0
    have hp_le : p * min 1 r ≤ (q * P.θL) * min 1 r := mul_le_mul_of_nonneg_right hp hr1_0
    have hstep1 : p * min 1 r - w * r ≤ (q * P.θL - w) * min 1 r := by linarith
    have hstep2 : (q * P.θL - w) * min 1 r ≤ max ((q * P.θL - w) * min S 1) 0 := by
      rcases le_or_gt 0 (q * P.θL - w) with hpos | hneg
      · exact le_trans (mul_le_mul_of_nonneg_left hr1_S1 hpos) (le_max_left _ _)
      · exact le_trans (mul_nonpos_of_nonpos_of_nonneg hneg.le hr1_0) (le_max_right _ _)
    rw [hpay]
    refine ⟨le_trans hstep1 hstep2, fun hp_lt hPiL_pos => ?_⟩
    rcases eq_or_lt_of_le hr1_0 with hr1_eq | hr1_pos
    · rw [← hr1_eq, mul_zero, zero_sub]
      have hwr0 : 0 ≤ w * r := mul_nonneg hw0 hr0
      linarith
    · have hp_strict : p * min 1 r < (q * P.θL) * min 1 r :=
        mul_lt_mul_of_pos_right hp_lt hr1_pos
      have hPiL_coeff : 0 ≤ q * P.θL - w := by
        have hS1_0 : 0 ≤ min S 1 := le_min hS zero_le_one
        by_contra hc
        have hc_lt : q * P.θL - w < 0 := lt_of_not_ge hc
        have := mul_nonpos_of_nonpos_of_nonneg hc_lt.le hS1_0
        linarith
      have h2 : (q * P.θL - w) * min 1 r ≤ (q * P.θL - w) * min S 1 :=
        mul_le_mul_of_nonneg_left hr1_S1 hPiL_coeff
      linarith
  have h_caseH : ∀ α Q p : ℝ, 0 ≤ α → 0 ≤ Q → q * P.θL < p → p ≤ q * P.θH →
      P.stepOnePayoff q w α S Q p ≤ (q * P.θH - w) * min α S ∧
      (p < q * P.θH → 0 < (q * P.θH - w) * min α S →
        P.stepOnePayoff q w α S Q p < (q * P.θH - w) * min α S) := by
    intro α Q p hα0 hQ hpL hpH
    let r := min Q S
    have hr0 : 0 ≤ r := le_min hQ hS
    have hrS : r ≤ S := min_le_right Q S
    have hpay : P.stepOnePayoff q w α S Q p = p * min α r - w * r := by
      unfold Params.stepOnePayoff Params.demand
      rw [if_neg (not_le_of_gt hpL), if_pos hpH, zero_add]
    have hrα_0 : 0 ≤ min α r := le_min hα0 hr0
    have hrα_r : min α r ≤ r := min_le_right α r
    have hrα_S : min α r ≤ min α S := min_le_min_left α hrS
    have hwr : w * min α r ≤ w * r := mul_le_mul_of_nonneg_left hrα_r hw0
    have hp_le : p * min α r ≤ (q * P.θH) * min α r := mul_le_mul_of_nonneg_right hpH hrα_0
    have hstep1 : p * min α r - w * r ≤ (q * P.θH - w) * min α r := by linarith
    have hstep2 : (q * P.θH - w) * min α r ≤ (q * P.θH - w) * min α S :=
      mul_le_mul_of_nonneg_left hrα_S hwH.le
    rw [hpay]
    refine ⟨le_trans hstep1 hstep2, fun hp_lt hPiH_pos => ?_⟩
    rcases eq_or_lt_of_le hrα_0 with hrα_eq | hrα_pos
    · rw [← hrα_eq, mul_zero, zero_sub]
      have hwr0 : 0 ≤ w * r := mul_nonneg hw0 hr0
      linarith
    · have hp_strict : p * min α r < (q * P.θH) * min α r :=
        mul_lt_mul_of_pos_right hp_lt hrα_pos
      linarith
  have h_case0 : ∀ α Q p : ℝ, 0 ≤ Q → q * P.θH < p →
      P.stepOnePayoff q w α S Q p ≤ 0 := by
    intro α Q p hQ hpH
    have hr0 : 0 ≤ min Q S := le_min hQ hS
    unfold Params.stepOnePayoff Params.demand
    rw [if_neg (not_le_of_gt (lt_trans hqLH hpH)), if_neg (not_le_of_gt hpH), add_zero,
      min_eq_left hr0, mul_zero, zero_sub]
    have : 0 ≤ w * min Q S := mul_nonneg hw0 hr0
    linarith
  have h_part1 : ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      IsGreatest {v : ℝ | ∃ Q p : ℝ, 0 ≤ Q ∧ 0 ≤ p ∧ v = P.stepOnePayoff q w α S Q p}
        (max (max ((q * P.θH - w) * min α S) ((q * P.θL - w) * min S 1)) 0) := by
    intro α hα0 _hα1
    refine ⟨?_, ?_⟩
    · rcases max_choice (max ((q * P.θH - w) * min α S) ((q * P.θL - w) * min S 1)) 0 with h1 | h0
      · rw [h1]
        rcases max_choice ((q * P.θH - w) * min α S) ((q * P.θL - w) * min S 1) with hH | hL
        · rw [hH]
          exact ⟨min α S, q * P.θH, le_min hα0 hS, hqH.le, (h_attH α hα0).symm⟩
        · rw [hL]
          exact ⟨min S 1, q * P.θL, le_min hS zero_le_one, hqL.le, (h_attL α).symm⟩
      · rw [h0]
        exact ⟨0, 0, le_refl 0, le_refl 0, (h_att0 α).symm⟩
    · rintro v ⟨Q, p, hQ, _hp, rfl⟩
      rcases le_or_gt p (q * P.θL) with hpL | hpL
      · have hb := (h_caseL α Q p hQ hpL).1
        exact le_trans hb (max_le (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _))
      · rcases le_or_gt p (q * P.θH) with hpH | hpH
        · exact le_trans (h_caseH α Q p hα0 hQ hpL hpH).1
            (le_trans (le_max_left _ _) (le_max_left _ _))
        · exact le_trans (h_case0 α Q p hQ hpH) (le_max_right _ _)
  have h_uniq_H : ∀ α : ℝ, 0 ≤ α → 0 < (q * P.θH - w) * min α S →
      (q * P.θL - w) * min S 1 < (q * P.θH - w) * min α S →
      ∀ Q p : ℝ, 0 ≤ Q → 0 ≤ p →
      (∀ Q' p' : ℝ, 0 ≤ Q' → 0 ≤ p' →
        P.stepOnePayoff q w α S Q' p' ≤ P.stepOnePayoff q w α S Q p) →
      p = q * P.θH := by
    intro α hα0 hPiH_pos hL_lt_H Q p hQ _hp hopt
    have hgeH : (q * P.θH - w) * min α S ≤ P.stepOnePayoff q w α S Q p := by
      rw [← h_attH α hα0]
      exact hopt (min α S) (q * P.θH) (le_min hα0 hS) hqH.le
    rcases le_or_gt p (q * P.θL) with hpL | hpL
    · exfalso
      have hb := (h_caseL α Q p hQ hpL).1
      have hlt : max ((q * P.θL - w) * min S 1) 0 < (q * P.θH - w) * min α S :=
        max_lt hL_lt_H hPiH_pos
      linarith
    · rcases le_or_gt p (q * P.θH) with hpH | hpH
      · rcases eq_or_lt_of_le hpH with hp_eq | hp_lt
        · exact hp_eq
        · exfalso
          have hlt := (h_caseH α Q p hα0 hQ hpL hp_lt.le).2 hp_lt hPiH_pos
          linarith
      · exfalso
        have hb := h_case0 α Q p hQ hpH
        linarith
  refine ⟨h_part1, ?_, ?_, ?_⟩
  · intro hS_pos Q p hQ hp hopt
    have hmin_pos : 0 < min P.αg S := lt_min hαg0 hS_pos
    have hPiH_pos : 0 < (q * P.θH - w) * min P.αg S := mul_pos hwH hmin_pos
    have hL_lt_H : (q * P.θL - w) * min S 1 < (q * P.θH - w) * min P.αg S := by
      rcases le_or_gt (q * P.θL - w) 0 with hL0 | hL_pos
      · have hS1_0 : 0 ≤ min S 1 := le_min hS zero_le_one
        exact lt_of_le_of_lt (mul_nonpos_of_nonpos_of_nonneg hL0 hS1_0) hPiH_pos
      · rcases le_or_gt S P.αg with hSα | hSα
        · have hS1 : min S 1 = S := min_eq_left (le_trans hSα hαg1.le)
          have hαS : min P.αg S = S := min_eq_right hSα
          rw [hS1, hαS]
          exact mul_lt_mul_of_pos_right (by linarith) hS_pos
        · have hαS : min P.αg S = P.αg := min_eq_left hSα.le
          have hS1_le : (q * P.θL - w) * min S 1 ≤ q * P.θL - w := by
            have := mul_le_mul_of_nonneg_left (min_le_right S 1) hL_pos.le
            linarith
          have hqαg : q * P.θL < q * (P.αg * P.θH) := mul_lt_mul_of_pos_left hαg_gt hq
          have hwαg : w * P.αg ≤ w := by
            have := mul_le_mul_of_nonneg_left hαg1.le hw0
            linarith
          rw [hαS]
          linarith
    exact h_uniq_H P.αg hαg0.le hPiH_pos hL_lt_H Q p hQ hp hopt
  · intro hH_lt_L Q p hQ _hp hopt
    have hPiH_nonneg : 0 ≤ (q * P.θH - w) * min P.αb S :=
      mul_nonneg hwH.le (le_min hαb0.le hS)
    have hPiL_pos : 0 < (q * P.θL - w) * min S 1 := lt_of_le_of_lt hPiH_nonneg hH_lt_L
    have hgeL : (q * P.θL - w) * min S 1 ≤ P.stepOnePayoff q w P.αb S Q p := by
      rw [← h_attL P.αb]
      exact hopt (min S 1) (q * P.θL) (le_min hS zero_le_one) hqL.le
    rcases le_or_gt p (q * P.θL) with hpL | hpL
    · rcases eq_or_lt_of_le hpL with hp_eq | hp_lt
      · exact hp_eq
      · exfalso
        have hlt := (h_caseL P.αb Q p hQ hpL).2 hp_lt hPiL_pos
        linarith
    · rcases le_or_gt p (q * P.θH) with hpH | hpH
      · exfalso
        have hb := (h_caseH P.αb Q p hαb0.le hQ hpL hpH).1
        linarith
      · exfalso
        have hb := h_case0 P.αb Q p hQ hpH
        linarith
  · intro hL_lt_H Q p hQ hp hopt
    have hS_pos : 0 < S := by
      rcases eq_or_lt_of_le hS with rfl | hpos
      · exfalso
        rw [min_eq_left zero_le_one, mul_zero, min_eq_right hαb0.le, mul_zero] at hL_lt_H
        exact lt_irrefl 0 hL_lt_H
      · exact hpos
    have hPiH_pos : 0 < (q * P.θH - w) * min P.αb S :=
      mul_pos hwH (lt_min hαb0 hS_pos)
    exact h_uniq_H P.αb hαb0.le hPiH_pos hL_lt_H Q p hQ hp hopt
