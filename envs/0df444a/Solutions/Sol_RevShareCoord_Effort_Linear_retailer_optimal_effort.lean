-- Prove2me | solution 1 for RevShareCoord.Effort.Linear.retailer_optimal_effort
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T10:09:40.95827+00:00
-- url     : https://prove2.me/submissions/7a60b987-a3a7-46fc-8fc0-6bd8544698b1

import Mathlib
import Definitions.Def_RevShareCoord_Effort_Linear

open RevShareCoord.Effort.Linear in
theorem solution (τ φ w q : ℝ) (hτ0 : 0 ≤ τ) (hτ1 : τ < 1)
    (hφ0 : 0 < φ) (hφ1 : φ ≤ 1) (hq : 0 ≤ q) :
    0 ≤ effort τ φ q ∧
    IsMaxOn (fun e => retailerProfit τ φ w q e) (Set.Ici 0) (effort τ φ q) ∧
    (∀ e : ℝ, 0 ≤ e → IsMaxOn (fun e' => retailerProfit τ φ w q e') (Set.Ici 0) e →
      e = effort τ φ q) ∧
    MonotoneOn (fun φ' => effort τ φ' q) (Set.Ici 0) := by
  have key : ∀ e : ℝ, retailerProfit τ φ w q (effort τ φ q) - retailerProfit τ φ w q e
      = (e - effort τ φ q) ^ 2 := by
    intro e
    simp only [retailerProfit, revenue, price, effort]
    ring
  have hnn : 0 ≤ effort τ φ q := by
    unfold effort
    exact mul_nonneg (mul_nonneg hφ0.le hτ0) hq
  refine ⟨hnn, ?_, ?_, ?_⟩
  · intro e _
    have := key e
    have h2 : 0 ≤ (e - effort τ φ q) ^ 2 := sq_nonneg _
    show retailerProfit τ φ w q e ≤ retailerProfit τ φ w q (effort τ φ q)
    linarith
  · intro e _ hmax
    have h1 : retailerProfit τ φ w q (effort τ φ q) ≤ retailerProfit τ φ w q e :=
      hmax (show effort τ φ q ∈ Set.Ici (0:ℝ) from hnn)
    have := key e
    have h3 : (e - effort τ φ q) ^ 2 = 0 := by
      nlinarith [sq_nonneg (e - effort τ φ q)]
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h3
    linarith
  · intro a _ b _ hab
    show effort τ a q ≤ effort τ b q
    unfold effort
    have : 0 ≤ τ * q := mul_nonneg hτ0 hq
    nlinarith
