-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.sum_casCoef
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:18:03.605888+00:00
-- url     : https://prove2.me/submissions/30302996-3c2d-4c2d-9dff-1e063671fd7a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution (μ : Fin n → ℤ) (lam : Fin n → ℝ) (hμ : IsMu lam μ) :
    ∑ a, ∑ b, casCoef μ a b = casVal lam := by
  have hcard : ∀ a : Fin n, (((univ.filter fun b : Fin n => b < a).card : ℕ) : ℝ) -
      (((univ.filter fun b : Fin n => a < b).card : ℕ) : ℝ) = -2 * rho n a := by
    intro a
    rw [Finset.filter_gt_eq_Iio, Finset.filter_lt_eq_Ioi, Fin.card_Iio, Fin.card_Ioi]
    have ha : 1 + (a : ℕ) ≤ n := by have := a.isLt; omega
    rw [Nat.sub_sub, Nat.cast_sub ha]
    simp only [rho]
    push_cast
    ring
  have hrow : ∀ a, ∑ b, casCoef μ a b = (μ a : ℝ) ^ 2 +
      ∑ b, ((if b < a then (μ a : ℝ) else 0) - if b < a then (μ b : ℝ) else 0) := by
    intro a
    rw [show (μ a : ℝ) ^ 2 = ∑ b, (if a = b then (μ a : ℝ) ^ 2 else 0) by simp, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold casCoef
    split_ifs <;> ring
  have hswap : ∑ a : Fin n, ∑ b : Fin n, (if b < a then (μ b : ℝ) else 0) =
      ∑ a : Fin n, ∑ b : Fin n, (if a < b then (μ a : ℝ) else 0) := Finset.sum_comm
  have hA : ∀ a : Fin n, ∑ b : Fin n, (if b < a then (μ a : ℝ) else 0) =
      (μ a : ℝ) * (((univ.filter fun b : Fin n => b < a).card : ℕ) : ℝ) := by
    intro a
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hB : ∀ a : Fin n, ∑ b : Fin n, (if a < b then (μ a : ℝ) else 0) =
      (μ a : ℝ) * (((univ.filter fun b : Fin n => a < b).card : ℕ) : ℝ) := by
    intro a
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
  calc ∑ a, ∑ b, casCoef μ a b = ∑ a, (μ a : ℝ) ^ 2 + ((∑ a, ∑ b, if b < a then (μ a : ℝ) else 0) -
        ∑ a, ∑ b, if b < a then (μ b : ℝ) else 0) := by
        simp only [hrow, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = ∑ a, ((μ a : ℝ) ^ 2 + (μ a : ℝ) * (-2 * rho n a)) := by
        rw [hswap, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hA, hB, ← hcard]
        ring
    _ = casVal lam := by
        simp only [casVal, nsq, dot, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [hμ a]
        ring
end ReciprocityTheory.ChartRestriction.DS.S7
