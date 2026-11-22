-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.recursiveCostBound_base_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:58:38.308365+00:00
-- url     : https://prove2.me/submissions/397edb39-a2a0-487e-b4c4-7c386fdbc609

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_recursiveCostBound_base

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {K : ℝ} {n0 : ℕ} :
    ∀ n : ℕ, n < n0 → 2 ^ n * minPile n ≤ recursiveCostBound K n0 n := by
  intro n hn
  rw [recursiveCostBound_base hn]
end PebblingLean.Hypercube.PaperParameters
