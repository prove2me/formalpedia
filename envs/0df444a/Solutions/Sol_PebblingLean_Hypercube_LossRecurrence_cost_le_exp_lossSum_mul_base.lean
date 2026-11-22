-- Prove2me | solution 1 for PebblingLean.Hypercube.LossRecurrence.cost_le_exp_lossSum_mul_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:08:09.751946+00:00
-- url     : https://prove2.me/submissions/c3e18e32-06a3-42d5-9ba4-3582a8b54e06

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundRecurrence
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Theorems.Thm_PebblingLean_Hypercube_LossRecurrence_cost_le_lossProduct_mul_base
public import Theorems.Thm_PebblingLean_Hypercube_LossRecurrence_lossProduct_le_exp_lossSum

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.LossRecurrence
namespace PebblingLean.Hypercube.LossRecurrence
theorem _root_.solution
    {next : ℕ → ℕ} {loss R : ℕ → ℝ} {n0 k n : ℕ} {B : ℝ}
    (hloss : ∀ n : ℕ, 0 ≤ loss n)
    (hB : 0 ≤ B)
    (hstep :
      ∀ n : ℕ, n0 ≤ n → R n ≤ (1 + loss n) * R (next n))
    (hactive : ActiveFor next n0 k n)
    (hbase : R (iterate next k n) ≤ B) :
    R n ≤ Real.exp (lossSum next loss k n) * B := by
  have hrec := cost_le_lossProduct_mul_base
    (next := next) (loss := loss) (R := R) (n0 := n0)
    (k := k) (n := n) (B := B) hloss hstep hactive hbase
  have hprod := lossProduct_le_exp_lossSum
    (next := next) (loss := loss) hloss k n
  exact hrec.trans (mul_le_mul_of_nonneg_right hprod hB)
end PebblingLean.Hypercube.LossRecurrence
