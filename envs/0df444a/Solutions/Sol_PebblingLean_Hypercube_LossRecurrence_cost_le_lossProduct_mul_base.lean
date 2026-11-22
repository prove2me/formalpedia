-- Prove2me | solution 1 for PebblingLean.Hypercube.LossRecurrence.cost_le_lossProduct_mul_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:07:19.61093+00:00
-- url     : https://prove2.me/submissions/904e9ce2-6808-4835-9a0a-b68781ba9ce1

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundRecurrence
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Theorems.Thm_PebblingLean_Hypercube_LossRecurrence_lossProduct_nonneg
public import Theorems.Thm_PebblingLean_Hypercube_LossRecurrence_cost_le_lossProduct

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
    (hstep :
      ∀ n : ℕ, n0 ≤ n → R n ≤ (1 + loss n) * R (next n))
    (hactive : ActiveFor next n0 k n)
    (hbase : R (iterate next k n) ≤ B) :
    R n ≤ lossProduct next loss k n * B := by
  have hrec := cost_le_lossProduct (next := next) (loss := loss) (R := R)
    (n0 := n0) hloss hstep k n hactive
  have hprod_nonneg := lossProduct_nonneg (next := next) (loss := loss) hloss k n
  exact hrec.trans (mul_le_mul_of_nonneg_left hbase hprod_nonneg)
end PebblingLean.Hypercube.LossRecurrence
