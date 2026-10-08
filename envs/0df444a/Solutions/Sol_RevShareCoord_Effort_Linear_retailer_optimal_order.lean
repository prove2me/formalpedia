-- Prove2me | solution 1 for RevShareCoord.Effort.Linear.retailer_optimal_order
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:19:29.292094+00:00
-- url     : https://prove2.me/submissions/ba8271ee-c77d-47b6-bd6d-2650431633fa

import Mathlib
import Definitions.Def_RevShareCoord_Effort_Linear

set_option autoImplicit false

namespace RevShareCoord.Effort.Linear

lemma p03db99b7_profit_identity (τ φ w q e Q : ℝ) :
    retailerProfit τ φ w q e =
      retailerProfit τ φ w Q (effort τ φ Q) - (φ - φ ^ 2 * τ ^ 2) * (q - Q) ^ 2
        - (e - φ * τ * q) ^ 2 + (q - Q) * (φ - w - 2 * (φ - φ ^ 2 * τ ^ 2) * Q) := by
  unfold retailerProfit revenue price effort
  ring

lemma p03db99b7_a_pos (τ φ : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1) (hφ0 : 0 < φ) (hφ1 : φ ≤ 1) :
    0 < φ - φ ^ 2 * τ ^ 2 := by
  have h1 : τ ^ 2 < 1 := by nlinarith
  have h2 : φ * τ ^ 2 < 1 := by nlinarith
  nlinarith

lemma p03db99b7_residual_nonpos (τ φ w q : ℝ) (ha : 0 < φ - φ ^ 2 * τ ^ 2) (hq : 0 ≤ q) :
    (q - orderQty τ φ w) * (φ - w - 2 * (φ - φ ^ 2 * τ ^ 2) * orderQty τ φ w) ≤ 0 := by
  unfold orderQty
  split_ifs with h
  · have : φ - w - 2 * (φ - φ ^ 2 * τ ^ 2) * ((φ - w) / (2 * (φ - φ ^ 2 * τ ^ 2))) = 0 := by
      generalize φ - φ ^ 2 * τ ^ 2 = a at ha ⊢
      have hne : a ≠ 0 := ha.ne'
      field_simp
      ring
    rw [this, mul_zero]
  · push Not at h
    nlinarith

lemma p03db99b7_profit_along (τ φ w q : ℝ) :
    retailerProfit τ φ w q (effort τ φ q) = q * (φ - q * (φ - φ ^ 2 * τ ^ 2) - w) := by
  unfold retailerProfit revenue price effort
  ring

lemma p03db99b7_orderQty_nonneg (τ φ w : ℝ) (ha : 0 < φ - φ ^ 2 * τ ^ 2) : 0 ≤ orderQty τ φ w := by
  unfold orderQty
  split_ifs with h
  · apply div_nonneg <;> linarith
  · exact le_refl 0

lemma p03db99b7_main_ineq (τ φ w q e : ℝ) (ha : 0 < φ - φ ^ 2 * τ ^ 2) (hq : 0 ≤ q) :
    retailerProfit τ φ w q e ≤
      retailerProfit τ φ w (orderQty τ φ w) (effort τ φ (orderQty τ φ w))
        - (φ - φ ^ 2 * τ ^ 2) * (q - orderQty τ φ w) ^ 2 - (e - φ * τ * q) ^ 2 := by
  rw [p03db99b7_profit_identity τ φ w q e (orderQty τ φ w)]
  have := p03db99b7_residual_nonpos τ φ w q ha hq
  linarith

end RevShareCoord.Effort.Linear

open RevShareCoord.Effort.Linear in
theorem solution (τ φ w : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hφ0 : 0 < φ) (hφ1 : φ ≤ 1) (hw : 0 ≤ w) :
    (∀ q : ℝ, retailerProfit τ φ w q (effort τ φ q) = q * (φ - q * (φ - φ ^ 2 * τ ^ 2) - w)) ∧
    (∀ x : ℝ × ℝ, IsRetailerResponse τ φ w x ↔
      x = (orderQty τ φ w, effort τ φ (orderQty τ φ w))) ∧
    (w < φ → 0 < orderQty τ φ w ∧
      retailerProfit τ φ w (orderQty τ φ w) (effort τ φ (orderQty τ φ w)) =
        (φ - w) ^ 2 / (4 * (φ - φ ^ 2 * τ ^ 2))) ∧
    (φ ≤ w → orderQty τ φ w = 0) := by
  have ha := p03db99b7_a_pos τ φ hτ0 hτ1 hφ0 hφ1
  have hQ := p03db99b7_orderQty_nonneg τ φ w ha
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q
    unfold retailerProfit revenue price effort
    ring
  · intro x
    have hmem : (orderQty τ φ w, effort τ φ (orderQty τ φ w)) ∈ quadrant := by
      refine ⟨Set.mem_Ici.mpr hQ, Set.mem_Ici.mpr ?_⟩
      unfold effort
      have : 0 ≤ φ * τ := mul_nonneg hφ0.le hτ0
      exact mul_nonneg this hQ
    constructor
    · rintro ⟨hx, hmax⟩
      have h1 := hmax hmem
      simp only [Set.mem_ofPred_eq] at h1
      have hq : 0 ≤ x.1 := hx.1
      have h2 := p03db99b7_main_ineq τ φ w x.1 x.2 ha hq
      have hsq1 : 0 ≤ (φ - φ ^ 2 * τ ^ 2) * (x.1 - orderQty τ φ w) ^ 2 :=
        mul_nonneg ha.le (sq_nonneg _)
      have hsq2 : 0 ≤ (x.2 - φ * τ * x.1) ^ 2 := sq_nonneg _
      have e1 : (φ - φ ^ 2 * τ ^ 2) * (x.1 - orderQty τ φ w) ^ 2 = 0 := by linarith
      have e2 : (x.2 - φ * τ * x.1) ^ 2 = 0 := by linarith
      have q_eq : x.1 = orderQty τ φ w := by
        rcases mul_eq_zero.mp e1 with h | h
        · linarith
        · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
          linarith
      have e_eq : x.2 = φ * τ * x.1 := by
        have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp e2
        linarith
      ext
      · exact q_eq
      · simp only [effort]
        rw [e_eq, q_eq]
    · rintro rfl
      refine ⟨hmem, ?_⟩
      intro y hy
      simp only [Set.mem_ofPred_eq]
      have hq : 0 ≤ y.1 := hy.1
      have h2 := p03db99b7_main_ineq τ φ w y.1 y.2 ha hq
      have hsq1 : 0 ≤ (φ - φ ^ 2 * τ ^ 2) * (y.1 - orderQty τ φ w) ^ 2 :=
        mul_nonneg ha.le (sq_nonneg _)
      have hsq2 : 0 ≤ (y.2 - φ * τ * y.1) ^ 2 := sq_nonneg _
      linarith
  · intro h
    have hQd : orderQty τ φ w = (φ - w) / (2 * (φ - φ ^ 2 * τ ^ 2)) := by
      unfold orderQty; rw [if_pos h]
    refine ⟨?_, ?_⟩
    · rw [hQd]; apply div_pos <;> linarith
    · rw [p03db99b7_profit_along, hQd]
      generalize φ - φ ^ 2 * τ ^ 2 = a at ha ⊢
      have hne : a ≠ 0 := ha.ne'
      field_simp
      ring
  · intro h
    unfold orderQty
    rw [if_neg (not_lt.mpr h)]
