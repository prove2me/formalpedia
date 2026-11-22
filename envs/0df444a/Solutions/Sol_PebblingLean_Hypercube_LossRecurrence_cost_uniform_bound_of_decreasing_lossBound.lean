-- Prove2me | solution 1 for PebblingLean.Hypercube.LossRecurrence.cost_uniform_bound_of_decreasing_lossBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:14:51.938091+00:00
-- url     : https://prove2.me/submissions/ee7a6483-8cd3-4f34-9d41-d3c0c0bff5a0

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundRecurrence
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Theorems.Thm_PebblingLean_Hypercube_LossRecurrence_cost_le_exp_lossBound_mul_base
public import Theorems.Thm_PebblingLean_Hypercube_LossRecurrence_exists_terminal_iterate_of_decreasing

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.LossRecurrence
namespace PebblingLean.Hypercube.LossRecurrence
theorem _root_.solution
    {next : ℕ → ℕ} {loss R : ℕ → ℝ} {n0 : ℕ} {B L : ℝ}
    (hloss : ∀ n : ℕ, 0 ≤ loss n)
    (hB : 0 ≤ B)
    (hnext : ∀ n : ℕ, n0 ≤ n → next n < n)
    (hstep :
      ∀ n : ℕ, n0 ≤ n → R n ≤ (1 + loss n) * R (next n))
    (hbase : ∀ n : ℕ, n < n0 → R n ≤ B)
    (hlossSum :
      ∀ n k : ℕ, ActiveFor next n0 k n →
        iterate next k n < n0 → lossSum next loss k n ≤ L)
    (n : ℕ) :
    R n ≤ Real.exp L * B := by
  rcases exists_terminal_iterate_of_decreasing
    (next := next) (n0 := n0) hnext n with
    ⟨k, hactive, hterm⟩
  exact cost_le_exp_lossBound_mul_base
    (next := next) (loss := loss) (R := R) (n0 := n0)
    (k := k) (n := n) (B := B) (L := L)
    hloss hB hstep hactive (hbase _ hterm)
    (hlossSum n k hactive hterm)
end PebblingLean.Hypercube.LossRecurrence
