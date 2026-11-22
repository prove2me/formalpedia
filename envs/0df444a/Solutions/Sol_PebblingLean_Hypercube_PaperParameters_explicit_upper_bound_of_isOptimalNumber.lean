-- Prove2me | solution 1 for PebblingLean.Hypercube.PaperParameters.explicit_upper_bound_of_isOptimalNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T07:11:59.560898+00:00
-- url     : https://prove2.me/submissions/12468376-42fa-49af-a1eb-7396bbe84182

module
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundLoss
public import Definitions.Def_LeanPool_PebblingLean_LowerBound
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Definitions.Def_LeanPool_PebblingLean_UpperBoundParameters
public import Theorems.Thm_PebblingLean_Hypercube_PaperParameters_hasRealUpperBound_explicitConstants

set_option autoImplicit true
@[expose] public section
public section
open PebblingLean
open PebblingLean.Hypercube
open PebblingLean.Hypercube.PaperParameters
namespace PebblingLean.Hypercube.PaperParameters
theorem _root_.solution {n k : ℕ}
    (hopt : Pebbling.IsOptimalNumber (graph n) k) :
    (k : ℝ) ≤
      (Real.exp (4 * loss explicitCutoff) *
        finiteBaseNormalizedBound (recursiveCostBound 217 explicitCutoff)
          explicitCutoff) *
        (((4 : ℝ) / 3) ^ n) := by
  rcases hasRealUpperBound_explicitConstants n with ⟨u, hu, hu_bound⟩
  rcases hu with ⟨D, hD_size, hD_solvable⟩
  have hsolvSize : Pebbling.HasSolvableSize (graph n) (Pebbling.size D) :=
    ⟨D, rfl, hD_solvable⟩
  have hk_size : k ≤ Pebbling.size D := by
    by_contra hnot
    have hlt : Pebbling.size D < k := Nat.lt_of_not_ge hnot
    exact (hopt.2 (Pebbling.size D) hlt) hsolvSize
  have hk_u : k ≤ u := hk_size.trans hD_size
  have hk_u_real : (k : ℝ) ≤ (u : ℝ) := by exact_mod_cast hk_u
  exact hk_u_real.trans hu_bound
end PebblingLean.Hypercube.PaperParameters
