-- Prove2me | solution 1 for TradeCreditIns.Cancelable.pi2_first_best
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-21T11:05:18.982246+00:00
-- url     : https://prove2.me/submissions/32a05bc7-f7da-4c5b-8b6b-c69c401453f3

import Mathlib
import Definitions.Def_TradeCreditIns_Cancelable_Model

open TradeCreditIns.Cancelable

namespace TCIP3Aux

theorem basic (P : Params) (hS : P.Standing)
    (hA1 : Assumption1 P) (hA2 : Assumption2 P)
    (hcφ : P.c ≤ φ P) (hr0 : (1 - P.β 1) * P.r ≤ P.r0) :
    0 < P.r ∧ P.βbar < P.β 1 ∧ 0 ≤ P.βbar ∧
    P.β 0 * P.r < (κstar P).p ∧ (κstar P).p < P.βbar * P.r ∧
    (κstar P).f = (κstar P).p ∧ (κstar P).δ = 0 ∧
    L P (P.r - (κstar P).δ - (κstar P).p) = 0 ∧
    0 ≤ L P ((κstar P).f - (κstar P).p) ∧
    P.θ 0 * (κstar P).p = P.c + P.θ 0 * P.β 0 * P.r ∧
    φ P = P.θ 1 * (P.r0 - (1 - P.β 1) * P.r) + P.θ 2 * (P.r0 - (1 - P.β 2) * P.r) := by
  obtain ⟨hθ, hsum, hθ0, hβ0, h01, h12, h2, hrr, hbar, hl, hc⟩ := hS
  unfold Assumption1 at hA1
  obtain ⟨hT0, hT⟩ := hA2
  rw [Fin.sum_univ_three] at hsum
  have hθ1 := hθ 1
  have hθ2 := hθ 2
  have hβbar : P.βbar = P.θ 0 * P.β 0 + P.θ 1 * P.β 1 + P.θ 2 * P.β 2 := by
    unfold Params.βbar; rw [Fin.sum_univ_three]
  rw [hβbar] at hbar
  have hr : 0 < P.r := by linarith
  have hbar0 : P.β 0 ≤ P.βbar := by
    rw [hβbar]; nlinarith [mul_nonneg hθ1 (sub_nonneg.2 h01.le),
      mul_nonneg hθ2 (sub_nonneg.2 (lt_trans h01 h12).le)]
  have hbar1 : P.βbar < P.β 1 := by
    rw [hβbar]; nlinarith
  have hbarnn : 0 ≤ P.βbar := le_trans hβ0 hbar0
  have hφ : φ P = P.θ 1 * (P.r0 - (1 - P.β 1) * P.r) +
      P.θ 2 * (P.r0 - (1 - P.β 2) * P.r) := by
    unfold φ; rw [Fin.sum_univ_three]
    have e0 : max (P.r0 - (1 - P.β 0) * P.r) 0 = 0 := by
      apply max_eq_right; rw [hβbar] at hbar0; nlinarith
    have e1 : max (P.r0 - (1 - P.β 1) * P.r) 0 = P.r0 - (1 - P.β 1) * P.r := by
      apply max_eq_left; linarith
    have e2 : max (P.r0 - (1 - P.β 2) * P.r) 0 = P.r0 - (1 - P.β 2) * P.r := by
      apply max_eq_left; linarith
    rw [e0, e1, e2]; ring
  have hpos12 : 0 < P.θ 1 + P.θ 2 := by
    by_contra hcon
    have e1 : P.θ 1 = 0 := by linarith
    have e2 : P.θ 2 = 0 := by linarith
    rw [hφ, e1, e2] at hcφ; linarith
  have hckey : P.c < P.θ 0 * (P.βbar - P.β 0) * P.r := by
    rw [hφ] at hcφ
    rw [hβbar]
    have : (P.θ 1 + P.θ 2) * P.r0 < (P.θ 1 + P.θ 2) *
        ((1 - (P.θ 0 * P.β 0 + P.θ 1 * P.β 1 + P.θ 2 * P.β 2)) * P.r) :=
      mul_lt_mul_of_pos_left hbar hpos12
    have e0 : P.θ 0 = 1 - P.θ 1 - P.θ 2 := by linarith
    rw [e0] at this ⊢
    nlinarith
  have hp : (κstar P).p = P.c / P.θ 0 + P.β 0 * P.r := rfl
  have hdiv : P.θ 0 * (P.c / P.θ 0) = P.c := by field_simp
  have hcd : 0 < P.c / P.θ 0 := div_pos hc hθ0
  have hcd2 : P.c / P.θ 0 < (P.βbar - P.β 0) * P.r := by
    rw [div_lt_iff₀ hθ0]; nlinarith
  refine ⟨hr, hbar1, hbarnn, ?_, ?_, rfl, rfl, ?_, ?_, ?_, hφ⟩
  · rw [hp]; linarith
  · rw [hp]; nlinarith
  · unfold L
    have : P.T - (P.r - (κstar P).δ - (κstar P).p) ≤ 0 := by
      have hd : (κstar P).δ = 0 := rfl
      rw [hd, hp]
      rw [hβbar] at hcd2
      nlinarith
    rw [max_eq_right this, mul_zero]
  · exact mul_nonneg hl (le_max_right _ _)
  · rw [hp, mul_add, hdiv]; ring

theorem cancels_iff (P : Params) (hS : P.Standing)
    (hA1 : Assumption1 P) (hA2 : Assumption2 P)
    (hcφ : P.c ≤ φ P) (hr0 : (1 - P.β 1) * P.r ≤ P.r0) (i : Fin 3) :
    Cancels P (κstar P) (P.β i) ↔ i ≠ 0 := by
  obtain ⟨hr, hb1, hbn, hp0, hpb, hf, hd, hL, -, -, -⟩ :=
    basic P hS hA1 hA2 hcφ hr0
  have hS' := hS
  obtain ⟨-, -, -, -, h01, h12, -, hrr, -, -, -⟩ := hS'
  have hsc : ∀ b, ShipsCovered P (κstar P) b := by
    intro b; unfold ShipsCovered; rw [hL, hd]; simp; linarith
  unfold Cancels
  rw [hf, hd, sub_zero]
  fin_cases i
  · simp; intro _; linarith
  · simp [hsc]; nlinarith
  · simp [hsc]; nlinarith

theorem ships_iff (P : Params) (hS : P.Standing)
    (hA1 : Assumption1 P) (hA2 : Assumption2 P)
    (hcφ : P.c ≤ φ P) (hr0 : (1 - P.β 1) * P.r ≤ P.r0) (i : Fin 3) :
    Ships P (κstar P) (P.β i) ↔ i = 0 := by
  obtain ⟨hr, hb1, hbn, hp0, hpb, hf, hd, hL, hL0, -, -⟩ :=
    basic P hS hA1 hA2 hcφ hr0
  have hS' := hS
  obtain ⟨-, -, -, hβ0, h01, h12, -, hrr, -, -, -⟩ := hS'
  unfold Assumption1 at hA1
  have hsc : ∀ b, ShipsCovered P (κstar P) b := by
    intro b; unfold ShipsCovered; rw [hL, hd]; simp; linarith
  have c0 : ¬ Cancels P (κstar P) (P.β 0) := by
    simpa using cancels_iff P hS hA1 hA2 hcφ hr0 0
  have c1 : Cancels P (κstar P) (P.β 1) := by
    simpa using cancels_iff P hS hA1 hA2 hcφ hr0 1
  have c2 : Cancels P (κstar P) (P.β 2) := by
    simpa using cancels_iff P hS hA1 hA2 hcφ hr0 2
  have s0 : Ships P (κstar P) (P.β 0) := by
    unfold Ships; rw [if_neg c0]; exact hsc _
  have s1 : ¬ Ships P (κstar P) (P.β 1) := by
    unfold Ships; rw [if_pos c1]; unfold ShipsUncovered
    nlinarith [mul_nonneg (le_of_lt (lt_of_le_of_lt hβ0 h01)) hL0]
  have s2 : ¬ Ships P (κstar P) (P.β 2) := by
    unfold Ships; rw [if_pos c2]; unfold ShipsUncovered
    nlinarith [mul_nonneg (le_of_lt (lt_trans (lt_of_le_of_lt hβ0 h01) h12)) hL0]
  fin_cases i
  · simpa using s0
  · simpa using s1
  · simpa using s2

theorem costEffort_eq (P : Params) (hS : P.Standing)
    (hA1 : Assumption1 P) (hA2 : Assumption2 P)
    (hcφ : P.c ≤ φ P) (hr0 : (1 - P.β 1) * P.r ≤ P.r0) :
    insurerCostEffort P (κstar P) = (κstar P).p := by
  obtain ⟨hr, hb1, hbn, hp0, hpb, hf, hd, hL, hL0, hθp, -⟩ :=
    basic P hS hA1 hA2 hcφ hr0
  have hS' := hS
  obtain ⟨-, hsum, -, -, -, -, -, hrr, -, -, -⟩ := hS'
  rw [Fin.sum_univ_three] at hsum
  have hsc : ∀ b, ShipsCovered P (κstar P) b := by
    intro b; unfold ShipsCovered; rw [hL, hd]; simp; linarith
  have c0 : ¬ Cancels P (κstar P) (P.β 0) := by
    simpa using cancels_iff P hS hA1 hA2 hcφ hr0 0
  have c1 : Cancels P (κstar P) (P.β 1) := by
    simpa using cancels_iff P hS hA1 hA2 hcφ hr0 1
  have c2 : Cancels P (κstar P) (P.β 2) := by
    simpa using cancels_iff P hS hA1 hA2 hcφ hr0 2
  unfold insurerCostEffort
  rw [Fin.sum_univ_three]
  simp only [c0, c1, c2, hsc, if_true, if_false, hf, hd, sub_zero]
  linear_combination (κstar P).p * hsum - hθp

theorem admissible (P : Params) (hS : P.Standing)
    (hA1 : Assumption1 P) (hA2 : Assumption2 P)
    (hcφ : P.c ≤ φ P) (hr0 : (1 - P.β 1) * P.r ≤ P.r0) :
    Admissible P (κstar P) := by
  obtain ⟨hr, hb1, hbn, hp0, hpb, hf, hd, hL, hL0, hθp, -⟩ :=
    basic P hS hA1 hA2 hcφ hr0
  have hS' := hS
  obtain ⟨-, -, -, hβ0, -, -, -, hrr, -, -, -⟩ := hS'
  have hsc : ∀ b, ShipsCovered P (κstar P) b := by
    intro b; unfold ShipsCovered; rw [hL, hd]; simp; linarith
  have hce := costEffort_eq P hS hA1 hA2 hcφ hr0
  refine ⟨⟨by rw [hd], by rw [hd]; linarith, by rw [hf]; nlinarith, by rw [hf]⟩,
    ⟨?_, by rw [hce, hf], by rw [hce]⟩,
    ⟨1, (cancels_iff P hS hA1 hA2 hcφ hr0 1).2 (by decide)⟩⟩
  unfold insurerCostKeep
  simp only [hsc, if_true, hce, hd, sub_zero]
  linarith

theorem payoff_eq (P : Params) (hS : P.Standing)
    (hA1 : Assumption1 P) (hA2 : Assumption2 P)
    (hcφ : P.c ≤ φ P) (hr0 : (1 - P.β 1) * P.r ≤ P.r0) :
    supplierPayoff P (κstar P) =
        P.θ 0 * (1 - P.β 0) * P.r + (P.θ 1 + P.θ 2) * P.r0 - P.c := by
  obtain ⟨hr, hb1, hbn, hp0, hpb, hf, hd, hL, hL0, hθp, -⟩ :=
    basic P hS hA1 hA2 hcφ hr0
  have hS' := hS
  obtain ⟨-, hsum, -, -, -, -, -, hrr, -, -, -⟩ := hS'
  rw [Fin.sum_univ_three] at hsum
  have hsc : ∀ b, ShipsCovered P (κstar P) b := by
    intro b; unfold ShipsCovered; rw [hL, hd]; simp; linarith
  have c0 : ¬ Cancels P (κstar P) (P.β 0) := by
    simpa using cancels_iff P hS hA1 hA2 hcφ hr0 0
  have c1 : Cancels P (κstar P) (P.β 1) := by
    simpa using cancels_iff P hS hA1 hA2 hcφ hr0 1
  have c2 : Cancels P (κstar P) (P.β 2) := by
    simpa using cancels_iff P hS hA1 hA2 hcφ hr0 2
  have u1 : ¬ ShipsUncovered P (κstar P) (P.β 1) := by
    have := (ships_iff P hS hA1 hA2 hcφ hr0 1)
    unfold Ships at this; rw [if_pos c1] at this; simpa using this
  have u2 : ¬ ShipsUncovered P (κstar P) (P.β 2) := by
    have := (ships_iff P hS hA1 hA2 hcφ hr0 2)
    unfold Ships at this; rw [if_pos c2] at this; simpa using this
  unfold supplierPayoff
  rw [Fin.sum_univ_three, if_neg c0, if_pos (hsc _), if_pos c1, if_pos c2,
    if_neg u1, if_neg u2, hL, hd, hf]
  linear_combination (κstar P).p * hsum - hθp

theorem firstBest_eq (P : Params) (hS : P.Standing)
    (hA1 : Assumption1 P) (hA2 : Assumption2 P)
    (hcφ : P.c ≤ φ P) (hr0 : (1 - P.β 1) * P.r ≤ P.r0) :
    P.θ 0 * (1 - P.β 0) * P.r + (P.θ 1 + P.θ 2) * P.r0 - P.c = firstBest P := by
  obtain ⟨hr, hb1, hbn, hp0, hpb, hf, hd, hL, hL0, hθp, hφ⟩ :=
    basic P hS hA1 hA2 hcφ hr0
  have hS' := hS
  obtain ⟨hθ, hsum, -, -, -, -, -, hrr, hbar, -, -⟩ := hS'
  unfold Assumption1 at hA1
  rw [Fin.sum_univ_three] at hsum
  have hβbar : P.βbar = P.θ 0 * P.β 0 + P.θ 1 * P.β 1 + P.θ 2 * P.β 2 := by
    unfold Params.βbar; rw [Fin.sum_univ_three]
  have hb0 : P.r0 ≤ (1 - P.β 0) * P.r := by nlinarith
  have ha : (1 - P.βbar) * P.r ≤
      P.θ 0 * (1 - P.β 0) * P.r + (P.θ 1 + P.θ 2) * P.r0 - P.c := by
    rw [hφ] at hcφ; rw [hβbar]
    have e0 : P.θ 0 = 1 - P.θ 1 - P.θ 2 := by linarith
    rw [e0]; nlinarith
  have hθ0 := hθ 0
  have hθ1 := hθ 1
  have hθ2 := hθ 2
  unfold firstBest
  apply le_antisymm
  · apply le_max_of_le_right
    refine Finset.le_sup'_of_le _ (Finset.mem_univ (fun i : Fin 3 => decide (i = 0))) ?_
    simp [Fin.sum_univ_three]
    linarith
  · apply max_le (max_le ha (by linarith))
    apply Finset.sup'_le
    intro s _
    simp only [Fin.sum_univ_three]
    have t0 : P.θ 0 * (if s 0 = true then (1 - P.β 0) * P.r else P.r0) ≤
        P.θ 0 * ((1 - P.β 0) * P.r) := by
      apply mul_le_mul_of_nonneg_left _ hθ0; split_ifs <;> linarith
    have t1 : P.θ 1 * (if s 1 = true then (1 - P.β 1) * P.r else P.r0) ≤
        P.θ 1 * P.r0 := by
      apply mul_le_mul_of_nonneg_left _ hθ1; split_ifs <;> linarith
    have t2 : P.θ 2 * (if s 2 = true then (1 - P.β 2) * P.r else P.r0) ≤
        P.θ 2 * P.r0 := by
      apply mul_le_mul_of_nonneg_left _ hθ2; split_ifs <;> linarith
    nlinarith

end TCIP3Aux

open TCIP3Aux in
theorem solution (P : Params) (hS : P.Standing)
    (hA1 : Assumption1 P) (hA2 : Assumption2 P)
    (hcφ : P.c ≤ φ P) (hr0 : (1 - P.β 1) * P.r ≤ P.r0) :
    supplierPayoff P (κstar P) =
        P.θ 0 * (1 - P.β 0) * P.r +
          (P.θ 1 + P.θ 2) * P.r0 - P.c ∧
    P.θ 0 * (1 - P.β 0) * P.r +
          (P.θ 1 + P.θ 2) * P.r0 - P.c = firstBest P :=
  ⟨payoff_eq P hS hA1 hA2 hcφ hr0, firstBest_eq P hS hA1 hA2 hcφ hr0⟩
