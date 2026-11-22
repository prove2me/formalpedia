-- Prove2me | solution 1 for PebblingLean.Hypercube.hasRealHypercubePebblingUpperBound_of_geometric_normalizedCost_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T06:12:02.395324+00:00
-- url     : https://prove2.me/submissions/72c76deb-e268-4a93-8f9d-841744accfb4

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundRecurrence
public import Mathlib.Algebra.Order.Algebra
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity.Finset
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Theorems.Thm_PebblingLean_Hypercube_LossRecurrence_cost_uniform_bound_of_geometric_loss_le_two
public import Theorems.Thm_PebblingLean_Hypercube_hasRealHypercubePebblingUpperBound_of_normalizedCost

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
namespace PebblingLean.Hypercube
theorem _root_.solution
    {costBound next : ℕ → ℕ} {loss : ℕ → ℝ} {n0 : ℕ}
    {B q M : ℝ}
    (hupper : HasHypercubePebblingUpperBound costBound)
    (hloss : ∀ n : ℕ, 0 ≤ loss n)
    (hB : 0 ≤ B)
    (hM : 0 ≤ M)
    (hq_nonneg : 0 ≤ q)
    (hq_half : q ≤ (1 : ℝ) / 2)
    (hnext : ∀ n : ℕ, n0 ≤ n → next n < n)
    (hstep :
      ∀ n : ℕ, n0 ≤ n →
        normalizedCost costBound n ≤
          (1 + loss n) * normalizedCost costBound (next n))
    (hbase :
      ∀ n : ℕ, n < n0 → normalizedCost costBound n ≤ B)
    (hdecay :
      ∀ n : ℕ, n0 ≤ n → n0 ≤ next n → loss n ≤ q * loss (next n))
    (hbound : ∀ n : ℕ, n0 ≤ n → loss n ≤ M) :
    HasRealHypercubePebblingUpperBound (Real.exp (2 * M) * B) := by
  have hnorm :
      ∀ n : ℕ,
        normalizedCost costBound n ≤ Real.exp (2 * M) * B :=
    LossRecurrence.cost_uniform_bound_of_geometric_loss_le_two
      (next := next) (loss := loss) (R := normalizedCost costBound)
      (n0 := n0) (B := B) (q := q) (M := M)
      hloss hB hM hq_nonneg hq_half hnext hstep hbase hdecay hbound
  exact hasRealHypercubePebblingUpperBound_of_normalizedCost hupper hnorm
end PebblingLean.Hypercube
