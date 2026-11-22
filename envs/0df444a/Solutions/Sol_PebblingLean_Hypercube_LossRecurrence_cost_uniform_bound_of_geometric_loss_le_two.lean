-- Prove2me | solution 1 for PebblingLean.Hypercube.LossRecurrence.cost_uniform_bound_of_geometric_loss_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:10:43.446261+00:00
-- url     : https://prove2.me/submissions/1f04162a-1ef8-4919-87d0-34fac87dcd24

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundRecurrence
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Theorems.Thm_PebblingLean_Hypercube_LossRecurrence_geomSum_le_two_of_le_half
public import Theorems.Thm_PebblingLean_Hypercube_LossRecurrence_cost_uniform_bound_of_geometric_loss

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.LossRecurrence
namespace PebblingLean.Hypercube.LossRecurrence
theorem _root_.solution
    {next : ℕ → ℕ} {loss R : ℕ → ℝ} {n0 : ℕ} {B q M : ℝ}
    (hloss : ∀ n : ℕ, 0 ≤ loss n)
    (hB : 0 ≤ B)
    (hM : 0 ≤ M)
    (hq_nonneg : 0 ≤ q)
    (hq_half : q ≤ (1 : ℝ) / 2)
    (hnext : ∀ n : ℕ, n0 ≤ n → next n < n)
    (hstep :
      ∀ n : ℕ, n0 ≤ n → R n ≤ (1 + loss n) * R (next n))
    (hbase : ∀ n : ℕ, n < n0 → R n ≤ B)
    (hdecay :
      ∀ n : ℕ, n0 ≤ n → n0 ≤ next n → loss n ≤ q * loss (next n))
    (hbound : ∀ n : ℕ, n0 ≤ n → loss n ≤ M) (n : ℕ) :
    R n ≤ Real.exp (2 * M) * B :=
  cost_uniform_bound_of_geometric_loss
    (next := next) (loss := loss) (R := R) (n0 := n0)
    (B := B) (q := q) (M := M) (G := 2)
    hloss hB hM hq_nonneg hnext hstep hbase hdecay hbound
    (geomSum_le_two_of_le_half hq_nonneg hq_half) n
end PebblingLean.Hypercube.LossRecurrence
