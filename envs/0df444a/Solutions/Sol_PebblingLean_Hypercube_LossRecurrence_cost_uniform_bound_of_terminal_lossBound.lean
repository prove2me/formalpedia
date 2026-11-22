-- Prove2me | solution 1 for PebblingLean.Hypercube.LossRecurrence.cost_uniform_bound_of_terminal_lossBound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:14:50.935877+00:00
-- url     : https://prove2.me/submissions/e4af6019-1ca3-4946-9950-19847b6f32c9

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundRecurrence
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Theorems.Thm_PebblingLean_Hypercube_LossRecurrence_cost_le_exp_lossBound_mul_base

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
    (hstep :
      ∀ n : ℕ, n0 ≤ n → R n ≤ (1 + loss n) * R (next n))
    (hbase : ∀ n : ℕ, n < n0 → R n ≤ B)
    (hterminal :
      ∀ n : ℕ, ∃ k : ℕ,
        ActiveFor next n0 k n ∧
          iterate next k n < n0 ∧
            lossSum next loss k n ≤ L)
    (n : ℕ) :
    R n ≤ Real.exp L * B := by
  rcases hterminal n with ⟨k, hactive, hterm, hsum⟩
  exact cost_le_exp_lossBound_mul_base
    (next := next) (loss := loss) (R := R) (n0 := n0)
    (k := k) (n := n) (B := B) (L := L)
    hloss hB hstep hactive (hbase _ hterm) hsum
end PebblingLean.Hypercube.LossRecurrence
