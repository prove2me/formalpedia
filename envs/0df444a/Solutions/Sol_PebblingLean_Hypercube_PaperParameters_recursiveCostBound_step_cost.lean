-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.recursiveCostBound_step_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:59:06.500815+00:00
-- url     : https://prove2.me/submissions/bb96cd28-8638-499d-9958-a02cd976e53b

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_recursiveCostBound_step
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_splitM_lt_of_four_mul_le

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {K : ℝ} {n0 : ℕ}
    (hn0_pos : 0 < n0)
    (hquarter : ∀ n : ℕ, n0 ≤ n → 4 * splitM K n ≤ n) :
    ∀ n : ℕ, n0 ≤ n →
      recursiveCostBound K n0 (splitM K n) * costMultiplier K n ≤
        recursiveCostBound K n0 n := by
  intro n hn
  have hsmall := splitM_lt_of_four_mul_le hn0_pos hn (hquarter n hn)
  rw [recursiveCostBound_step hn hsmall]
end PebblingLean.Hypercube.PaperParameters
