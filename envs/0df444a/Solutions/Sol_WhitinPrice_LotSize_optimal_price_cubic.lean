-- Prove2me | solution 1 for WhitinPrice.LotSize.optimal_price_cubic
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-08T02:39:06.949653+00:00
-- url     : https://prove2.me/submissions/c571f12f-5993-4288-808c-7fd2e82f1c62

import Theorems.Thm_WhitinPrice_LotSize_optimal_lot_size
import Theorems.Thm_WhitinPrice_LotSize_minimal_variable_cost
import Theorems.Thm_WhitinPrice_LotSize_stationary_price_cubic

set_option autoImplicit false
open WhitinPrice.LotSize

private theorem profit_at_eoq (S I C k f a b p : ℝ)
    (hS : 0 < S) (hI : 0 < I) (hC : 0 < C) (hD : 0 < demand a b p) :
    profit S I C k f a b p (Real.sqrt (2 * demand a b p * S / (I * C))) =
      reducedProfit S I C k f a b p := by
  unfold profit
  rw [minimal_variable_cost S I C k (demand a b p) hS hI hC hD]
  unfold reducedProfit demand
  have hrad : 2 * (a * p + b) * S * I * C = 2 * S * I * C * (a * p + b) := by ring
  rw [hrad]
  ring

theorem solution (S I C k f a b p Q : ℝ)
    (hS : 0 < S) (hI : 0 < I) (hC : 0 < C)
    (hD : 0 < demand a b p) (hQ : 0 < Q)
    (hmax : IsMaxOn
      (fun z : ℝ × ℝ => profit S I C k f a b z.1 z.2)
      {z : ℝ × ℝ | 0 < demand a b z.1 ∧ 0 < z.2} (p, Q)) :
    Q = Real.sqrt (2 * demand a b p * S / (I * C)) ∧
      8 * a ^ 3 * p ^ 3 + (16 * a ^ 2 * b - 8 * k * a ^ 3) * p ^ 2 +
        (10 * a * b ^ 2 - 12 * k * a ^ 2 * b + 2 * k ^ 2 * a ^ 3) * p +
        2 * b ^ 3 - 4 * k * a * b ^ 2 + 2 * k ^ 2 * a ^ 2 * b - S * I * C * a ^ 2 = 0 := by
  obtain ⟨hq, hmin⟩ := optimal_lot_size S I C k (demand a b p) hS hI hC hD
  have hcompare := hmax (show (p, Real.sqrt (2 * demand a b p * S / (I * C))) ∈ {z : ℝ × ℝ | 0 < demand a b z.1 ∧ 0 < z.2} from ⟨hD, hq⟩)
  have hQeq : Q = Real.sqrt (2 * demand a b p * S / (I * C)) := by
    apply (hmin Q hQ).2
    apply le_antisymm (hmin Q hQ).1
    change profit S I C k f a b p (Real.sqrt (2 * demand a b p * S / (I * C))) ≤
      profit S I C k f a b p Q at hcompare
    unfold profit at hcompare
    linarith
  refine ⟨hQeq, ?_⟩
  have hredmax : IsMaxOn (reducedProfit S I C k f a b) {x : ℝ | 0 < demand a b x} p := by
    intro x hx
    have hqx := (optimal_lot_size S I C k (demand a b x) hS hI hC hx).1
    have hcomp := hmax (show (x, Real.sqrt (2 * demand a b x * S / (I * C))) ∈
      {z : ℝ × ℝ | 0 < demand a b z.1 ∧ 0 < z.2} from ⟨hx, hqx⟩)
    change profit S I C k f a b x _ ≤ profit S I C k f a b p Q at hcomp
    rw [hQeq, profit_at_eoq S I C k f a b x hS hI hC hx,
      profit_at_eoq S I C k f a b p hS hI hC hD] at hcomp
    exact hcomp
  have hlocal : IsLocalMax (reducedProfit S I C k f a b) p := by
    apply hredmax.isLocalMax
    exact (isOpen_lt continuous_const (by unfold demand; fun_prop)).mem_nhds hD
  have hpos : 0 < 2 * S * I * C * (a * p + b) := by
    change 0 < a * p + b at hD
    positivity
  have hdiff : DifferentiableAt ℝ (reducedProfit S I C k f a b) p := by
    unfold reducedProfit
    fun_prop (disch := positivity)
  have hz := hlocal.hasDerivAt_eq_zero hdiff.hasDerivAt
  apply stationary_price_cubic S I C k f a b p hS hI hC hD
  simpa only [hz] using hdiff.hasDerivAt


