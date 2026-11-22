-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.explicit_bounds_of_isOptimalNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:12:54.48319+00:00
-- url     : https://prove2.me/submissions/460d2b43-8ee9-4f53-be32-1b338a832ee5

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_explicit_upper_bound_of_isOptimalNumber
public import Theorems.Thm_PebblingLean_Hypercube_lower_bound_of_isOptimalNumber


set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {n k : ℕ}
    (hopt : Pebbling.IsOptimalNumber (graph n) k) :
    ((4 : ℚ) / 3) ^ n ≤ (k : ℚ) ∧
      (k : ℝ) ≤
        (Real.exp (4 * loss explicitCutoff) *
          finiteBaseNormalizedBound (recursiveCostBound 217 explicitCutoff)
            explicitCutoff) *
          (((4 : ℝ) / 3) ^ n) :=
  ⟨lower_bound_of_isOptimalNumber hopt,
    explicit_upper_bound_of_isOptimalNumber hopt⟩
end PebblingLean.Hypercube.PaperParameters
