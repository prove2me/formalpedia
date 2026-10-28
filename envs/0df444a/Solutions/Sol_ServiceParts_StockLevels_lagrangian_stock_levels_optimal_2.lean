-- Prove2me | solution 2 for ServiceParts.StockLevels.lagrangian_stock_levels_optimal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T13:58:44.89592+00:00
-- url     : https://prove2.me/submissions/33b0b02a-acbd-46d1-ab67-33f7e04e1039

import Mathlib
import Definitions.Def_ServiceParts_StockLevels_Basic
import Definitions.Def_ServiceParts_StockLevels_CompoundPoissonDemand
import Definitions.Def_ServiceParts_StockLevels_Problems
import Theorems.Thm_ServiceParts_StockLevels_optimal_stock_criterion

-- carved verbatim out of submission d404c890-1bac-43b1-87e4-00d022f9080b, lines 472-479

section
open ServiceParts
open ServiceParts.StockLevels

lemma spc_sum_rc {ι : Type*} [Fintype ι] (d : ι → CompoundPoissonDemand) (c : ι → ℝ) (θ : ℝ)
    (s : ι → ℕ) : ∑ i, relaxedCost (d i) (c i) θ (s i) =
      totalBackorders d s + θ * totalInvestment d c s + θ * ∑ i, c i * (d i).mu := by
  unfold relaxedCost totalBackorders totalInvestment
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem lagrangian_stock_levels_optimal_core {ι : Type*} [Fintype ι]
    (d : ι → CompoundPoissonDemand) (c : ι → ℝ) (hc : ∀ i, 0 < c i) (θ : ℝ) (hθ : 0 < θ) :
    (∀ i, (stockSet (d i) (c i) θ).Nonempty) ∧
    ∀ sStar : ι → ℕ, (∀ i, IsLeast (stockSet (d i) (c i) θ) (sStar i)) →
      ∀ s : ι → ℕ, totalInvestment d c s ≤ totalInvestment d c sStar →
        totalBackorders d sStar ≤ totalBackorders d s := by
  refine ⟨fun i => (ServiceParts.StockLevels.optimal_stock_criterion (d i) (c i) θ (hc i) hθ).2.2.2.1, ?_⟩
  intro sStar hS s hinv
  have hsum : ∑ i, relaxedCost (d i) (c i) θ (sStar i) ≤ ∑ i, relaxedCost (d i) (c i) θ (s i) :=
    Finset.sum_le_sum fun i _ =>
      ((ServiceParts.StockLevels.optimal_stock_criterion (d i) (c i) θ (hc i) hθ).2.2.2.2 (sStar i) (hS i)).1 (s i)
  rw [spc_sum_rc, spc_sum_rc] at hsum
  nlinarith [mul_le_mul_of_nonneg_left hinv hθ.le]

end

section
open ServiceParts.StockLevels

theorem solution {ι : Type*} [Fintype ι]
    (d : ι → CompoundPoissonDemand) (c : ι → ℝ) (hc : ∀ i, 0 < c i) (θ : ℝ) (hθ : 0 < θ) :
    (∀ i, (stockSet (d i) (c i) θ).Nonempty) ∧
    ∀ sStar : ι → ℕ, (∀ i, IsLeast (stockSet (d i) (c i) θ) (sStar i)) →
      ∀ s : ι → ℕ, totalInvestment d c s ≤ totalInvestment d c sStar →
        totalBackorders d sStar ≤ totalBackorders d s := by
  exact lagrangian_stock_levels_optimal_core d c hc θ hθ

end
