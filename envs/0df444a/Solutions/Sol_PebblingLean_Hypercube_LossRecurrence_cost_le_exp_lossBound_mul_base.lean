-- Prove2me | solution 1 for PebblingLean.Hypercube.LossRecurrence.cost_le_exp_lossBound_mul_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:08:46.070723+00:00
-- url     : https://prove2.me/submissions/428a858f-02c8-4227-b1d4-12ba4a163ea6

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundRecurrence
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Theorems.Thm_PebblingLean_Hypercube_LossRecurrence_cost_le_exp_lossSum_mul_base

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.LossRecurrence
namespace PebblingLean.Hypercube.LossRecurrence
theorem _root_.solution
    {next : ℕ → ℕ} {loss R : ℕ → ℝ} {n0 k n : ℕ} {B L : ℝ}
    (hloss : ∀ n : ℕ, 0 ≤ loss n)
    (hB : 0 ≤ B)
    (hstep :
      ∀ n : ℕ, n0 ≤ n → R n ≤ (1 + loss n) * R (next n))
    (hactive : ActiveFor next n0 k n)
    (hbase : R (iterate next k n) ≤ B)
    (hsum : lossSum next loss k n ≤ L) :
    R n ≤ Real.exp L * B := by
  have hrec := cost_le_exp_lossSum_mul_base
    (next := next) (loss := loss) (R := R) (n0 := n0)
    (k := k) (n := n) (B := B) hloss hB hstep hactive hbase
  have hexp : Real.exp (lossSum next loss k n) ≤ Real.exp L :=
    Real.exp_le_exp.mpr hsum
  exact hrec.trans (mul_le_mul_of_nonneg_right hexp hB)
end PebblingLean.Hypercube.LossRecurrence
